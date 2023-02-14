(* Collapsed Tagged Proxy *)

(* Selective import to avoid universal inconsistency when importing QuickChick elsewhere
 * issue/solution: https://github.com/MetaCoq/metacoq/issues/580#issuecomment-1009602640 
 *)
From MetaCoq.Template Require Import
  utils         (* Utility functions *)
  monad_utils   (* Monadic notations *)
  uGraph        (* The graph of universes *)
  BasicAst      (* The basic AST structures *)
  Ast           (* The term AST *)
  AstUtils      (* Utilities on the AST *)
  Induction     (* Induction *)
  LiftSubst     (* Lifting and substitution for terms *)
  UnivSubst     (* Substitution of universe instances *)
  (* Typing *)        (* Typing judgment *)
  TemplateMonad (* The TemplateMonad *)
  Loader.

Require Import Coq.Strings.String.
Local Open Scope string_scope.




(* utils *)
Fixpoint zipWith {A B C : Type} (f : A -> B -> C) (la : list A) (lb : list B) : list C :=
  match la, lb with
  | a :: la', b :: lb' => f a b :: zipWith f la' lb'
  | _, _ => []
  end.

Fixpoint descNatList (n : nat) : list nat :=
  match n with
  | S n' => n :: (descNatList n')
  | 0 => [0]
  end.

Definition descRelList (n : nat) : list term :=
  map tRel (descNatList n).

Definition mapIndType {A} (f : term -> A) (ind : one_inductive_body) : A :=
  f ind.(ind_type).

Definition mapMindType {A} (f : term -> list A) (mind : mutual_inductive_body) : list A :=
  flat_map (mapIndType f) mind.(ind_bodies).




(* Universes and levels *)

Definition empty_uni := Universe.of_levels (inr Level.lSet).  

Definition levelsOfUni (uni : Universe.t) : list Level.t :=
  match uni with
  | Universe.lType lvlSet =>
      map fst (UnivExprSet.elements (Universe.t_set lvlSet))
  | _ => []
  end.

Fixpoint levelsOfType (tm : term) : list Level.t :=  
  match tm with
  | tSort uni => levelsOfUni uni
  | tProd _ tm1 tm2 => app (levelsOfType tm1) (levelsOfType tm2)
  | _ => []
  end.




(* Inds kernames *)

Fixpoint indKernamesOfType (tm : term) : list kername :=
  match tm with
  | tProd _ tm1 tm2 =>
      app (indKernamesOfType tm1) (indKernamesOfType tm2)
  | tApp (tInd ind _) _ =>
      [ind.(inductive_mind)]
  | _ =>
      []
  end.

  


(* Inductive template definitions etc. *)

Definition IndConstr := ((ident * term) * nat) : Type.

Definition mkInductive n mod_path name : inductive :=
  {| inductive_mind := (mod_path, name); inductive_ind := n |}.

Definition mkInductive0 := mkInductive 0.

Definition mkConstructTerm (mod_path: modpath) (name : ident) (idx : nat) : term :=
  tConstruct (mkInductive0 mod_path name) idx [].

Definition mkIndTerm (mod_path : modpath) (name : ident) (n : nat) :=
  tInd (mkInductive n mod_path name) [].

Definition mkIndTerm0 (mod_path : modpath) (name : ident) : term :=
  mkIndTerm mod_path name 0.

Definition mkMutInd (rel_name : ident) (ind_type : term) (ctors : list IndConstr) unis : mutual_inductive_body :=
  {|
    ind_finite := Finite;
    ind_npars := 0;
    ind_params := [];
    ind_bodies := 
    [{|
      ind_name := rel_name;
      ind_type := ind_type;
      ind_kelim := IntoAny;
      ind_ctors := ctors;
      ind_projs := [];
      ind_relevance := Relevant
    |}];
    ind_universes := unis;
    ind_variance := None
  |}.


(* Proxy references *)


Fixpoint proxyRefOfType (tm : term) (depth : nat) (tag_ref : term) (ind_idx : nat) : term :=
  match tm with
  | tProd bind type tm' =>
      tLambda bind type (proxyRefOfType tm' (depth + 1) tag_ref ind_idx)
  | tSort _ =>
      tApp
        (* reference to proxy *)
        (tRel (ind_idx + depth))
        [ match depth with
          (* Do not apply any arguments *)
          | 0 => tag_ref
          (* Apply arguments *)
          | S depth' => tApp tag_ref (descRelList depth')
          end
        ]
  | _ => tm
  end.

Definition proxyRefOfInd (body : one_inductive_body) (tag_ref : term) (ind_idx : nat) : term :=
  proxyRefOfType body.(ind_type) 0 tag_ref ind_idx.
    
Fixpoint proxyRefsOfInds (inds : list one_inductive_body) (tag_ref : nat -> term) (idx : nat) : list (nat -> term):=
  match inds with
  | ind :: inds' =>
      proxyRefOfInd ind (tag_ref idx) :: proxyRefsOfInds inds' tag_ref (idx + 1)
  | _ =>
      []
  end.

Definition proxyRefsOfMind (mind : mutual_inductive_body) (tag_ref : nat -> term) :=
  proxyRefsOfInds mind.(ind_bodies) tag_ref 0.




(* Tag type *)

Definition mkTagMutInd (rel_name : ident) (ctors : list IndConstr) unis lvls : mutual_inductive_body :=
  let (lSet, _) := monomorphic_udecl unis in
  let lvls := map (fun l => (l, true)) lvls in
  match lvls with
  | [] => 
      mkMutInd rel_name (tSort empty_uni) ctors unis
  | (l :: ls) => 
      mkMutInd rel_name (tSort (Universe.from_kernel_repr l ls)) ctors unis
  end.

Fixpoint toConstrType (term : term) (n : nat) : TemplateMonad (Ast.term * nat) :=
  match term with
  | tSort _ =>
      tmReturn (tRel n, n)
  | tProd aname var tm =>
      mlet (tm', n') <- toConstrType tm (n + 1);;
      tmReturn (tProd aname var tm', n')
  | _ => 
      tmFail "Type of term did not match tSort or tProd"
  end.

Definition toTagTypeConstr (mind_body : one_inductive_body) : TemplateMonad IndConstr :=
  constr_name <- tmFreshName (mind_body.(ind_name) ++ "_tag") ;;
  mlet (tm, n) <- toConstrType mind_body.(ind_type) 0 ;;
  tmReturn (constr_name, tm, n).

Definition mkProxyTagType (mind : mutual_inductive_body) : TemplateMonad (ident * mutual_inductive_body) :=
  match mind.(ind_bodies) with
  | [] =>
      tmFail "Inductive relation expected to have at least one body"
  | (ind :: _) as inds =>
      name <- tmFreshName (ind.(ind_name) ++ "_proxy_tag");;
      constrs <- monad_map toTagTypeConstr inds ;;

      tag_minds <- monad_map tmQuoteInductive (mapMindType indKernamesOfType mind);;
      let lvls := flat_map (mapMindType levelsOfType) (mind :: tag_minds) in
      let lSetLvls := LevelSetProp.of_list lvls in
      let (lSet, cSet) := monomorphic_udecl mind.(ind_universes) in
      let uni := Monomorphic_ctx (LevelSet.inter lSet lSetLvls, cSet) in
      let constrs_inv := rev constrs in
      let tag_decl := mkTagMutInd name constrs_inv uni lvls in
      tmReturn (name, tag_decl)
  end.







(* Proxy type *)

Definition mkProxyMutInd (tag_ind: inductive) rel_name ctors : mutual_inductive_body :=
  let type :=
    (tProd
    {| binder_name := nAnon; binder_relevance := Relevant |}
    (tInd tag_ind [])
    (tSort (Universe.of_levels (inl PropLevel.lProp))))
  in 
    mkMutInd rel_name type ctors (Monomorphic_ctx (LevelSet.empty, ConstraintSet.empty)).

Fixpoint toTagConstr (tag_term : nat -> term) (depth : nat) (constr : term) : term :=
  let rec := toTagConstr tag_term in
  match constr with
    (* handle the premises/result of a IndConstr separately *)
  | tProd bind t1 t2 =>
      tProd bind (rec depth t1) (rec (S depth) t2)
      (* a relation without arguments *)
  | tRel n =>
      if (Nat.ltb n depth) 
      then tRel n
      else tApp (tRel depth) [tag_term (n - depth)]
      (* an application of a relation and some arguments *)
  | tApp (tRel n) t2 as app =>
      if (Nat.ltb n depth) 
      then app
      else tApp (tRel depth) [tApp (tag_term (n - depth)) t2]
  | tApp tm tms =>
      tApp tm (map (rec depth) tms)
  | tLambda bind ty tm =>
      tLambda bind ty (rec (depth + 1) tm)

  (* not verified *)
  | tEvar ev args =>
      tEvar ev (map (rec depth) args)
  | tCast t kind v =>
      tCast (rec depth t) kind (rec depth v)
  | tLetIn na def def_ty body =>
      tLetIn na (rec depth def) def_ty (rec (S depth) body)
  | tCase ci type_info discr branches =>
      tCase ci type_info (rec depth discr) (map (fun b => (fst b, rec depth (snd b))) branches)

  (* poke-match *)
  | tm => tm
  end.

Definition mkProxyTypeConstr (tag_name : ident) (mod_path : modpath) (constr : IndConstr)  : IndConstr :=
  match constr with
  | (name, term, arity) =>
      let name' := (name ++ "_proxy") in
      let mk_constr_term := mkConstructTerm mod_path tag_name in
      let term' := toTagConstr mk_constr_term 0 term in
      (name', term', arity)
  end.

Definition mkProxyType (mind : mutual_inductive_body) (tag_name : ident) (mod_path : modpath) : option (ident * mutual_inductive_body) :=
  match mind.(ind_bodies) with
  | [] =>
      None
  | (ind :: _) as inds =>     
      let name := (ind.(ind_name) ++ "_proxy") in
      let type := mkInductive0 mod_path tag_name in
      let ctors := flat_map ind_ctors inds in
      let ctors' := map (mkProxyTypeConstr tag_name mod_path) ctors in
      Some (name, mkProxyMutInd type name ctors')
  end.



(* soundness definition *)  

Fixpoint tagCaseFromTypeRec (n : nat) (tm : term) (ind_ref : term) : nat * term :=
  match tm with
  | tProd bind type tm' =>
      let (n', tm'') := tagCaseFromTypeRec (n + 1) tm' ind_ref in
      (n', tLambda bind type tm'')
  | _ =>
      match n with
      | S n' => (n, tApp ind_ref (descRelList n'))
      | 0 => (0, ind_ref)
      end
  end.

Definition tagCaseFromType (tm : term) (ind_ref : term) := 
  tagCaseFromTypeRec 0 tm ind_ref.

Definition getName (mind : mutual_inductive_body) : ident :=
  nth_default "" (map ind_name mind.(ind_bodies)) 0.
  
Definition mkSoundDefinition (ind_mod_path : modpath) (mod_path : modpath) (ind_def : mutual_inductive_body) : term :=
  let ind_name := getName ind_def in
  let proxy_name := ind_name ++ "_proxy" in
  let tag_name := proxy_name ++ "_tag" in
    (tProd
      {|
        binder_name := nNamed "tag";
        binder_relevance := Relevant
      |}
      (mkIndTerm0 mod_path tag_name)
      (tProd
        {|
          binder_name := nAnon;
          binder_relevance := Relevant
        |}
        (tApp
        (mkIndTerm0 mod_path proxy_name)
          [tRel 0])
        (tCase
          (mkInductive0 mod_path tag_name, 0, Relevant)
          (tLambda
            {|
              binder_name := nNamed "tag";
              binder_relevance := Relevant
            |}
            (mkIndTerm0 mod_path tag_name)
              (tSort (Universe.of_levels (inl PropLevel.lProp)))
            )
            (tRel 1)
            (
              let tagCaseWithoutInds := (map (fun x => tagCaseFromType (ind_type x)) ind_def.(ind_bodies)) in

              (* The following reverse is necessary since the tag IndConstr are in opposite order*)
              let inds := map (mkIndTerm ind_mod_path ind_name) (descNatList (List.length tagCaseWithoutInds - 1)) in
              (zipWith Basics.apply (rev tagCaseWithoutInds) inds)
            )
          )
      )
    )
.

(* Derivation of tag and proxy type *)

Fixpoint deriveCTProxyTerm tm :=
  match tm with
  | tApp tm1 tm2 =>
      deriveCTProxyTerm tm1
  | tInd ind_term _ =>
      mod_path <- tmCurrentModPath tt;;
      let (ind_mod_path, ind_name) := inductive_mind ind_term in
      mind <- tmQuoteInductive (ind_mod_path, ind_name);; 
      
      mlet (tag_name, tag_term) <- mkProxyTagType mind ;;
      tmMkInductive' tag_term;;

      match mkProxyType mind tag_name mod_path with 
      | Some (proxy_name, proxy_decl) =>
          tmMkInductive' proxy_decl;;
          
          (* Proxy soundness proof *)
          let sound_def := mkSoundDefinition (ind_mod_path) mod_path mind in
          t' <- tmUnquote sound_def ;;
          t'' <- tmEval (unfold (Common_kn "my_projT2")) (my_projT2 t') ;;
          tmDefinitionRed (proxy_name ++ "_sound_type") (Some (unfold (Common_kn "my_projT1"))) t'';;

          (* Necessary, because of the antics of using TemplateMonad *)
          tmReturn unit
      | _ =>
          tmFail "failed to make a proxy type"
      end
   | _ => 
      tmPrint tm;;
      tmFail "The provided term is not an inductive"
  end.

Definition deriveCTProxy {A} (ind : A) :=
  tm <- tmQuote ind ;;
  deriveCTProxyTerm tm.

Ltac deriveCTProxy_sound Hints :=
  intros tag H; induction H; subst; eauto with Hints. 
