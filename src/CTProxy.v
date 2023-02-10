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
Local Open Scope program_scope.


Fixpoint zipWith {A B C : Type} (f : A -> B -> C) (la : list A) (lb : list B) : list C :=
  match la, lb with
  | a :: la', b :: lb' => f a b :: zipWith f la' lb'
  | _, _ => []
  end.



(* Universes and levels *)

Definition empty_uni := Universe.of_levels (inr Level.lSet).  


Definition levelsOfUni (uni : Universe.t) : list Level.t :=
  match uni with
  | Universe.lType lvlSet =>
      map fst (UnivExprSet.elements (Universe.t_set lvlSet))
  | _ => []
  end.

Fixpoint uniOfType (tm : term) : list Level.t :=
  match tm with
  | tProd _ _ tm => uniOfType tm
  | tSort uni    => levelsOfUni uni
  | _            => []
  end.

Fixpoint uniFromType (type : term) : list Level.t :=  
    match type with
    | tSort uni => 
        levelsOfUni uni
    | tProd _ tm1 tm2 =>
        app (uniFromType tm1) (uniFromType tm2)
    | _ =>
        []
    end.

Definition lvlsFromInd (ind : one_inductive_body) : list Level.t :=
  uniFromType ind.(ind_type).

Definition lvlsFromMind (mind : mutual_inductive_body) : list Level.t := 
  flat_map lvlsFromInd mind.(ind_bodies).






(* Inds kernames *)

Fixpoint indsFromTerm (tm : term) : list kername :=
  match tm with
  | tProd _ tm1 tm2 =>
      app (indsFromTerm tm1) (indsFromTerm tm2)
  | tApp (tInd ind _) _ =>
      [ind.(inductive_mind)]
  | _ =>
      []
  end.

Definition indsFromInd (ind : one_inductive_body) : list kername :=
  indsFromTerm ind.(ind_type).

Definition indsFromMind (mind : mutual_inductive_body) : list kername :=
  List.concat (map indsFromInd mind.(ind_bodies)).



  


(* Inductive template definitions etc. *)

Definition Constr := ((ident * term) * nat) : Type.

Definition mkInductiveN (mod_path : modpath) (name : ident) (n : nat) : inductive :=
  {| inductive_mind := (mod_path, name); inductive_ind := n |}.

Definition mkInductive (mod_path : modpath) (name : ident) : inductive :=
  mkInductiveN mod_path name 0.

Definition mkConstructTerm (mod_path: modpath) (name : ident) (idx : nat) : term :=
  tConstruct (mkInductive mod_path name) idx [].

Definition mkIndTermN (mod_path : modpath) (name : ident) (n : nat) :=
  tInd (mkInductiveN mod_path name n) [].

Definition mkIndTerm (mod_path : modpath) (name : ident) : term :=
  mkIndTermN mod_path name 0.


Definition mutIndTemplate (indType : term) (relName : ident) (ctors : list Constr) unis : mutual_inductive_body :=
  {|
    ind_finite := Finite;
    ind_npars := 0;
    ind_params := [];
    ind_bodies := 
    [{|
      ind_name := relName;
      ind_type := indType;
      ind_kelim := IntoAny;
      ind_ctors := ctors;
      ind_projs := [];
      ind_relevance := Relevant
    |}];
    ind_universes := unis;
    ind_variance := None
  |}.


(* Proxy references *)

Fixpoint descNatList (n : nat) : list nat :=
  match n with
  | S n' => n :: (descNatList n')
  | 0 => [0]
  end.

Definition descRelList (n : nat) : list term :=
  map tRel (descNatList n).

Fixpoint proxyRefOfTypeTerm (tm : term) (depth : nat) (tag_ref : term) (ind_idx : nat) : term :=
  match tm with
  | tProd bind type tm' =>
      tLambda bind type (proxyRefOfTypeTerm tm' (depth + 1) tag_ref ind_idx)
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
  proxyRefOfTypeTerm body.(ind_type) 0 tag_ref ind_idx.
    
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

Definition mkTagMutInd (relName : ident) (ctors : list Constr) unis lvls : mutual_inductive_body :=
  let (lSet, _) := monomorphic_udecl unis in
  let lvls := map (fun l => (l, true)) lvls in
  match lvls with
  | [] => mutIndTemplate (tSort empty_uni) relName ctors unis
  | (l :: ls) => mutIndTemplate (tSort (Universe.from_kernel_repr l ls)) relName ctors unis
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

Definition toTagTypeConstr (mind_body : one_inductive_body) : TemplateMonad Constr :=
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

      tag_minds <- monad_map tmQuoteInductive (indsFromMind mind);;
      let lvls := flat_map lvlsFromMind (mind :: tag_minds) in
      let lSetLvls := LevelSetProp.of_list lvls in
      let (lSet, cSet) := monomorphic_udecl mind.(ind_universes) in
      let uni := Monomorphic_ctx (LevelSet.inter lSet lSetLvls, cSet) in

      (* This invert aligns the constructor order with the DeBruijn indices later on *)
      (* FIXME: no longer necessary after changes have been made *)
      let constrs_inv := rev constrs in
      let tag_decl := mkTagMutInd name constrs_inv uni lvls in
      tmReturn (name, tag_decl)
  end.







(* Proxy type *)

Definition mkProxyMutInd (tagInd: inductive) relName ctors : mutual_inductive_body :=
  let type :=
    (tProd
    {| binder_name := nAnon; binder_relevance := Relevant |}
    (tInd tagInd [])
    (tSort (Universe.of_levels (inl PropLevel.lProp))))
  in 
    mutIndTemplate type relName ctors (Monomorphic_ctx (LevelSet.empty, ConstraintSet.empty)).

Fixpoint toTagConstr (tagTerm : nat -> term) (depth : nat) (constr : term) : term :=
  let rec := toTagConstr tagTerm in
  match constr with
    (* handle the premises/result of a constructor separately *)
  | tProd bind t1 t2 =>
      tProd bind (rec depth t1) (rec (S depth) t2)
      (* a relation without arguments *)
  | tRel n =>
      if (Nat.ltb n depth) 
      then tRel n
      else tApp (tRel depth) [tagTerm (n - depth)]
      (* an application of a relation and some arguments *)
  | tApp (tRel n) t2 as app =>
      if (Nat.ltb n depth) 
      then app
      else tApp (tRel depth) [tApp (tagTerm (n - depth)) t2]
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

Definition mkProxyTypeConstr (tag_name : ident) (mod_path : modpath) (constr : Constr)  : Constr :=
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
      let type := mkInductive mod_path tag_name in
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
  
Definition mkSoundDefinition (mod_path : modpath) (ind_def : mutual_inductive_body) : term :=
  let ind_name := getName ind_def in
  let proxy_name := ind_name ++ "_proxy" in
  let tag_name := proxy_name ++ "_tag" in
    (tProd
      {|
        binder_name := nNamed "tag";
        binder_relevance := Relevant
      |}
      (mkIndTerm mod_path tag_name)
      (tProd
        {|
          binder_name := nAnon;
          binder_relevance := Relevant
        |}
        (tApp
        (mkIndTerm mod_path proxy_name)
          [tRel 0])
        (tCase
          (mkInductive mod_path tag_name, 0, Relevant)
          (tLambda
            {|
              binder_name := nNamed "tag";
              binder_relevance := Relevant
            |}
            (mkIndTerm mod_path tag_name)
              (tSort (Universe.of_levels (inl PropLevel.lProp)))
            )
            (tRel 1)
            (
              let tagCaseWithoutInds := (map (fun x => tagCaseFromType (ind_type x)) ind_def.(ind_bodies)) in

              (* The following reverse is necessary since the tag constructor are in opposite order*)
              let inds := map (mkIndTermN mod_path ind_name) (descNatList (List.length tagCaseWithoutInds - 1)) in
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
      mind <- tmQuoteInductive (inductive_mind ind_term);; 
      
      mlet (tag_name, tag_term) <- mkProxyTagType mind ;;
      tmMkInductive' tag_term;;

      match mkProxyType mind tag_name mod_path with 
      | Some (proxy_name, proxy_decl) =>
          tmMkInductive' proxy_decl;;
          
          (* Proxy soundness proof *)
          let sound_def := mkSoundDefinition mod_path mind in

          sound_def' <- tmEval lazy sound_def;;
          tmPrint sound_def';;

          t' <- tmUnquote sound_def ;;
          t'' <- tmEval (unfold (Common_kn "my_projT2")) (my_projT2 t') ;;
          tmDefinitionRed (proxy_name ++ "_sound_type") (Some (unfold (Common_kn "my_projT1"))) t'';;
          tmMsg ""
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
