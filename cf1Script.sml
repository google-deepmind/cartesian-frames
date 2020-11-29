open HolKernel boolLib bossLib Parse cf0Theory categoryTheory functorTheory limitTheory
     dep_rewrite combinTheory sumTheory pairTheory pred_setTheory
     listTheory rich_listTheory ASCIInumbersTheory

val _ = new_theory"cf1";

Datatype:
  chu_morphism_map = <| map_agent: act -> act; map_env: act -> act |>
End

val chu_morphism_map_component_equality = theorem"chu_morphism_map_component_equality";

Definition is_chu_morphism_def:
  is_chu_morphism c1 c2 m ⇔
    extensional m.map_agent c1.agent ∧
    extensional m.map_env c2.env ∧
    (∀e. e ∈ c2.env ⇒ m.map_env e ∈ c1.env) ∧
    (∀a. a ∈ c1.agent ⇒ m.map_agent a ∈ c2.agent) ∧
    (∀a f. a ∈ c1.agent ∧ f ∈ c2.env ⇒
       c1.eval a (m.map_env f) = c2.eval (m.map_agent a) f)
End

Definition chu_id_morphism_map_def:
  chu_id_morphism_map c =
    <| map_agent := restrict I c.agent; map_env := restrict I c.env |>
End

Theorem is_chu_morphism_id[simp]:
  is_chu_morphism c c (chu_id_morphism_map c)
Proof
  rw[is_chu_morphism_def, chu_id_morphism_map_def]
  \\ rw[restrict_def]
QED

Definition mk_chu_morphism_def:
  mk_chu_morphism c1 c2 f =
    <| dom := c1; cod := c2; map :=
      <| map_agent := restrict f.map_agent c1.agent;
         map_env := restrict f.map_env c2.env |> |>
End

Theorem mk_chu_morphism_dom_cod[simp]:
  (mk_chu_morphism c1 c2 f).dom = c1 ∧
  (mk_chu_morphism c1 c2 f).cod = c2
Proof
  rw[mk_chu_morphism_def]
QED

Definition chu_objects_def:
  chu_objects w = { c | wf c ∧ c.world = w }
End

(* TODO: should these be temp? or moved elsewhere? *)
Type functor[pp] = ``:('a,'b,'c,'d) functor``;
Type nat_trans[pp] = ``:('a, 'b, 'c, 'd) nat_trans``;
(* -- *)

Type chu_morphism[pp] = ``:('w cf, 'w cf, chu_morphism_map) morphism``;

Definition pre_chu_def:
  pre_chu w =
    <| obj := chu_objects w;
       mor := { m | m.dom ∈ chu_objects w ∧ m.cod ∈ chu_objects w ∧
                    is_chu_morphism m.dom m.cod m.map };
       id_map := chu_id_morphism_map ;
       comp := λm1 m2. <| map_agent := restrict (m2.map.map_agent o m1.map.map_agent) m1.dom.agent ;
                          map_env := restrict (m1.map.map_env o m2.map.map_env) m2.cod.env |>
     |>
End

Definition chu_def:
  chu = mk_cat o pre_chu
End

Theorem is_category_chu[simp]:
  is_category (chu w)
Proof
  rw[chu_def]
  \\ simp[category_axioms_def]
  \\ conj_tac >- simp[pre_chu_def]
  \\ conj_tac >- simp[pre_chu_def]
  \\ conj_tac >- (
    simp[maps_to_in_def]
    \\ gen_tac \\ strip_tac
    \\ simp[id_in_def, restrict_def]
    \\ fs[pre_chu_def]
    \\ simp[is_chu_morphism_def] )
  \\ conj_tac >- (
    simp[pre_chu_def, id_in_def, restrict_def, compose_in_def, composable_in_def]
    \\ simp[morphism_component_equality, chu_morphism_map_component_equality]
    \\ simp[FUN_EQ_THM]
    \\ simp[is_chu_morphism_def, extensional_def]
    \\ simp[chu_id_morphism_map_def, restrict_def]
    \\ rw[] \\ rw[])
  \\ conj_tac >- (
    simp[pre_chu_def, id_in_def, restrict_def, compose_in_def, composable_in_def]
    \\ simp[morphism_component_equality, chu_morphism_map_component_equality]
    \\ simp[FUN_EQ_THM]
    \\ simp[is_chu_morphism_def, extensional_def]
    \\ simp[chu_id_morphism_map_def, restrict_def]
    \\ rw[] \\ rw[])
  \\ conj_tac >- (
    simp[composable_in_def, compose_in_def, restrict_def]
    \\ rw[pre_chu_def, restrict_def] \\ rw[]
    \\ fs[is_chu_morphism_def, extensional_def])
  \\ rw[maps_to_in_def, compose_in_def, restrict_def, composable_in_def]
  \\ fs[pre_chu_def, is_chu_morphism_def, restrict_def, extensional_def]
QED

Theorem chu_obj[simp]:
  (chu w).obj = chu_objects w
Proof
  rw[chu_def, pre_chu_def]
QED

Theorem chu_mor[simp]:
  (chu w).mor = (pre_chu w).mor
Proof
  rw[chu_def]
QED

Theorem chu_id_map:
  (chu w).id_map = restrict chu_id_morphism_map (chu_objects w)
Proof
  rw[chu_def, pre_chu_def, mk_cat_def]
QED

Theorem chu_id[simp]:
  x ∈ chu_objects w ⇒
  (id x -: chu w).dom = x ∧
  (id x -: chu w).cod = x ∧
  (id x -: chu w).map = chu_id_morphism_map x
Proof
  rw[id_in_def]
  \\ rw[restrict_def, chu_id_map]
QED

Theorem chu_comp[simp]:
  f ≈> g -: chu w ⇒
  (chu w).comp f g = (pre_chu w).comp f g
Proof
  rw[composable_in_def, chu_def, mk_cat_def, restrict_def]
QED

Definition swap_def:
  swap c = <| world := c.world; agent := c.env; env := c.agent;
              eval := flip c.eval |>
End

Theorem swap_components[simp]:
  (swap c).world = c.world ∧
  (swap c).agent = c.env ∧
  (swap c).env = c.agent ∧
  (swap c).eval a e = c.eval e a
Proof
  rw[swap_def]
QED

Theorem swap_in_chu_objects[simp]:
  swap c ∈ chu_objects w ⇔ c ∈ chu_objects w
Proof
  rw[chu_objects_def, wf_def]
  \\ metis_tac[]
QED

Theorem swap_swap[simp]:
  swap (swap c) = c
Proof
  rw[swap_def, cf_component_equality]
  \\ rw[FUN_EQ_THM]
QED

Definition swap_morphism_map_def:
  swap_morphism_map m = <| map_agent := m.map_env; map_env := m.map_agent |>
End

Theorem swap_morphism_map_components[simp]:
  (swap_morphism_map m).map_agent = m.map_env ∧
  (swap_morphism_map m).map_env = m.map_agent
Proof
  rw[swap_morphism_map_def]
QED

Theorem is_chu_morphism_swap[simp]:
  is_chu_morphism (swap c2) (swap c1) (swap_morphism_map m) ⇔
  is_chu_morphism c1 c2 m
Proof
  rw[is_chu_morphism_def] \\ metis_tac[]
QED

Definition swap_morphism_def:
  swap_morphism m =
    <| dom := swap m.dom;
       cod := swap m.cod;
       map := swap_morphism_map m.map |>
End

Theorem swap_morphism_components[simp]:
  (swap_morphism m).dom = swap m.dom ∧
  (swap_morphism m).cod = swap m.cod ∧
  (swap_morphism m).map = swap_morphism_map m.map
Proof
  rw[swap_morphism_def]
QED

Theorem swap_morphism_idem[simp]:
  swap_morphism (swap_morphism m) = m
Proof
  rw[swap_morphism_def, morphism_component_equality]
  \\ rw[swap_morphism_map_def, chu_morphism_map_component_equality]
QED

Theorem swap_morphism_inj[simp]:
  swap_morphism m1 = swap_morphism m2 ⇔ m1 = m2
Proof
  rw[swap_morphism_def, morphism_component_equality]
  \\ simp[swap_def, swap_morphism_map_def]
  \\ simp[cf_component_equality, chu_morphism_map_component_equality]
  \\ simp[FUN_EQ_THM]
  \\ metis_tac[]
QED

Theorem swap_morphism_id:
  c ∈ chu_objects w ⇒
  swap_morphism (id c -: chu w) = id (swap c) -: chu w
Proof
  rw[id_in_def, restrict_def, swap_morphism_def, morphism_component_equality] \\ rfs[]
  \\ rw[swap_morphism_map_def, chu_id_map]
  \\ rw[chu_morphism_map_component_equality, restrict_def, chu_id_morphism_map_def]
QED

Theorem swap_morphism_comp:
  f ≈> g -: chu w ⇒
  swap_morphism (g o f -: chu w) =
  swap_morphism g o swap_morphism f -: (op_cat (chu w))
Proof
  simp[compose_in_def, restrict_def, composable_in_def, compose_thm]
  \\ simp[pre_chu_def]
  \\ rw[] \\ fs[]
  \\ simp[morphism_component_equality]
  \\ simp[chu_def, mk_cat_def, restrict_def, composable_in_def]
  \\ simp[pre_chu_def, chu_morphism_map_component_equality]
QED

Theorem swap_morphism_composable:
  (swap_morphism f ≈> swap_morphism g) ⇔ f ≈> g
Proof
  rw[composable_def]
  \\ rw[cf_component_equality]
  \\ rw[swap_def, FUN_EQ_THM]
  \\ metis_tac[]
QED

Theorem swap_morphism_composable_in:
  (swap_morphism f ≈> swap_morphism g -: chu w) ⇔ (f ≈> g -: op_cat (chu w))
Proof
  rw[composable_in_def]
  \\ simp[pre_chu_def]
  \\ simp[cf_component_equality]
  \\ rw[EQ_IMP_THM] \\ fs[]
  \\ fs[FUN_EQ_THM]
QED

Theorem op_mor_swap_morphism:
  op_mor (swap_morphism m) = swap_morphism (op_mor m)
Proof
  rw[swap_morphism_def, op_mor_def]
QED

Definition swap_functor_def:
  swap_functor w =
    mk_functor
      <| dom := chu w;
         cod := op_cat (chu w);
         map := swap_morphism |>
End

Theorem is_functor_swap[simp]:
  is_functor (swap_functor w)
Proof
  simp[swap_functor_def]
  \\ simp[functor_axioms_def]
  \\ conj_tac
  >- (
    simp[maps_to_in_def]
    \\ simp[pre_chu_def]
    \\ simp[morf_def]
    \\ gen_tac \\ strip_tac
    \\ simp[objf_def]
    \\ simp[morf_def]
    \\ simp[swap_morphism_id]
    \\ simp[id_inj]
    \\ SELECT_ELIM_TAC
    \\ conj_tac >- metis_tac[swap_in_chu_objects]
    \\ SELECT_ELIM_TAC
    \\ conj_tac >- metis_tac[swap_in_chu_objects]
    \\ gen_tac \\ strip_tac
    \\ imp_res_tac id_inj \\ rfs[]
    \\ gen_tac \\ strip_tac
    \\ imp_res_tac id_inj \\ rfs[])
  \\ conj_tac
  >- (
    simp[morf_def]
    \\ simp[swap_morphism_id]
    \\ metis_tac[swap_in_chu_objects])
  \\ simp[morf_def]
  \\ simp[swap_morphism_comp]
QED

Definition op_swap_functor_def:
  op_swap_functor w =
    mk_functor <| dom := (chu w)°; cod := chu w; map := swap_morphism|>
End

(* essentially the same proof as is_functor_swap *)
Theorem is_functor_op_swap[simp]:
  is_functor (op_swap_functor w)
Proof
  simp[functor_axioms_def, op_swap_functor_def]
  \\ conj_tac
  >- (
    simp[maps_to_in_def]
    \\ simp[pre_chu_def]
    \\ simp[morf_def]
    \\ gen_tac \\ strip_tac
    \\ simp[objf_def]
    \\ simp[morf_def]
    \\ simp[swap_morphism_id]
    \\ simp[id_inj]
    \\ SELECT_ELIM_TAC
    \\ conj_tac >- metis_tac[swap_in_chu_objects]
    \\ SELECT_ELIM_TAC
    \\ conj_tac >- metis_tac[swap_in_chu_objects]
    \\ gen_tac \\ strip_tac
    \\ imp_res_tac id_inj \\ rfs[]
    \\ gen_tac \\ strip_tac
    \\ imp_res_tac id_inj \\ rfs[])
  \\ conj_tac
  >- (
    simp[morf_def]
    \\ simp[swap_morphism_id]
    \\ metis_tac[swap_in_chu_objects])
  \\ simp[morf_def]
  \\ rpt strip_tac
  \\ drule swap_morphism_comp
  \\ simp[op_cat_compose_in]
  \\ strip_tac
  \\ simp[Once(GSYM op_mor_swap_morphism)]
  \\ simp[GSYM op_mor_swap_morphism]
  \\ DEP_REWRITE_TAC[GSYM op_cat_compose_in]
  \\ simp[]
  \\ simp[swap_morphism_composable_in]
QED

Theorem cat_iso_pair_swap_functor:
  cat_iso_pair (swap_functor w) (op_swap_functor w)
Proof
  simp[cat_iso_pair_def]
  \\ conj_asm1_tac >- rw[swap_functor_def, op_swap_functor_def]
  \\ qmatch_goalsub_abbrev_tac`f ◎ g`
  \\ `f ≈> g` by rw[]
  \\ `g ≈> f` by rw[Abbr`g`, Abbr`f`, swap_functor_def, op_swap_functor_def]
  \\ simp[morphism_component_equality] \\ fs[]
  \\ simp[functor_comp_def, id_functor_def]
  \\ simp[mk_functor_def]
  \\ simp[restrict_def]
  \\ simp[FUN_EQ_THM]
  \\ rw[] \\ simp[Abbr`f`, Abbr`g`]
  \\ fs[swap_functor_def, op_swap_functor_def]
  \\ fs[mk_functor_def, restrict_def]
  \\ fs[pre_chu_def] \\ rw[]
  \\ `F` suffices_by rw[]
  \\ pop_assum mp_tac \\ simp[]
  \\ qexists_tac`op_mor (swap_morphism e)`
  \\ simp[]
QED

Theorem iso_pair_between_cats_chu_op:
  iso_pair_between_cats (chu w) (swap_functor w) (op_swap_functor w) (op_cat (chu w))
Proof
  rw[iso_pair_between_cats_def, cat_iso_pair_swap_functor]
  \\ rw[swap_functor_def]
QED

Theorem iso_cats_chu_op:
  iso_cats (chu w) (op_cat (chu w))
Proof
  rw[iso_cats_def]
  \\ metis_tac[iso_pair_between_cats_chu_op]
QED

(*
can't get this to work - maybe it's not true
Theorem op_mor_swap_functor_mk_functor:
  op_mor (swap_functor w) = op_swap_functor w
Proof
  rw[morphism_component_equality]
  \\ rw[swap_functor_def, op_swap_functor_def]
  \\ rw[mk_functor_def]
  \\ rw[restrict_def]
  \\ rw[FUN_EQ_THM]
  \\ qmatch_abbrev_tac`COND b1 _ _ = COND b2 _ _`
  \\ `b1 = b2` suffices_by rw[]
  \\ simp[Abbr`b1`, Abbr`b2`]
  \\ simp[pre_chu_def]
  \\ `∀x. e = x° ⇔  x = e°`
  by (
    rw[morphism_component_equality]
    \\ metis_tac[] )
*)

Theorem swap_functor_objf[simp]:
  c ∈ chu_objects w ⇒
    (swap_functor w) @@ c = swap c ∧
    (op_swap_functor w) @@ c = swap c
Proof
  rw[swap_functor_def, op_swap_functor_def]
  \\ rw[objf_def, morf_def]
  \\ SELECT_ELIM_TAC
  \\ (conj_tac >- metis_tac[swap_morphism_id, swap_in_chu_objects])
  \\ simp[swap_morphism_id]
  \\ rw[]
  \\ qspec_then`chu w`match_mp_tac id_inj
  \\ simp[]
QED

Theorem swap_functor_morf[simp]:
  (f ∈ (pre_chu w).mor ⇒ (swap_functor w) ## f = swap_morphism f )∧
  (g ∈ ((pre_chu w)°).mor ⇒ (op_swap_functor w) ## g = swap_morphism g)
Proof
  rw[swap_functor_def, op_swap_functor_def]
  \\ simp[morf_def]
QED

Theorem swap_functor_idem[simp]:
  c ∈ chu_objects w ⇒
    (swap_functor w) @@ ((swap_functor w) @@ c) = c ∧
    (op_swap_functor w) @@ ((op_swap_functor w) @@ c) = c
Proof
  rw[]
QED

Definition encode_pair_def:
  encode_pair (s1, s2) =
    toString (LENGTH s1) ++ ":" ++ s1 ++ s2
End

Definition decode_pair_def:
  decode_pair s =
    let (n, s) = SPLITP ((=)#":") s in
    let s = TL s in
    let n = toNum n in
    (TAKE n s, DROP n s)
End

Theorem decode_encode_pair[simp]:
  decode_pair (encode_pair p) = p
Proof
  Cases_on`p`
  \\ rw[encode_pair_def]
  \\ rw[decode_pair_def]
  \\ rewrite_tac[GSYM APPEND_ASSOC]
  \\ once_rewrite_tac[SPLITP_APPEND]
  \\ qmatch_goalsub_rename_tac`_ = (s1, s2)`
  \\ IF_CASES_TAC
  >- (
    qspec_then`LENGTH s1`assume_tac EVERY_isDigit_num_to_dec_string
    \\ fs[EXISTS_MEM, EVERY_MEM]
    \\ `F` suffices_by rw[]
    \\ res_tac \\ pop_assum mp_tac
    \\ EVAL_TAC )
  \\ simp[SPLITP]
  \\ simp[toNum_toString]
  \\ simp[TAKE_APPEND, DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Theorem encode_pair_inj[simp]:
  encode_pair p1 = encode_pair p2 ⇔ p1 = p2
Proof
  metis_tac[decode_encode_pair]
QED

Definition encode_sum_def:
  encode_sum (INL s) = toString (LENGTH s) ++ "l" ++ s ∧
  encode_sum (INR s) = toString (LENGTH s) ++ "r" ++ s
End

Definition decode_sum_def:
  decode_sum s =
    let (n, r) = SPLITP ((~) o isDigit) s in
    let (t, r) = (HD r, TL r) in
    let n = toNum n in
    if t = #"l" ∧ LENGTH r = n then INL r else
    if t = #"r" ∧ LENGTH r = n then INR r else ARB
End

Theorem decode_encode_sum[simp]:
  decode_sum (encode_sum s) = s
Proof
  Cases_on`s` \\ rw[encode_sum_def, decode_sum_def]
  \\ rewrite_tac[GSYM APPEND_ASSOC]
  \\ once_rewrite_tac[SPLITP_APPEND]
  \\ rewrite_tac[GSYM NOT_EVERY, EVERY_isDigit_num_to_dec_string]
  \\ simp[SPLITP, EVAL``isDigit #"l"``, EVAL ``isDigit #"r"``]
  \\ simp[toNum_toString]
QED

Theorem encode_sum_inj[simp]:
  encode_sum x = encode_sum y ⇔ x = y
Proof
  metis_tac[decode_encode_sum]
QED

Definition sum_eval_def:
  sum_eval f1 f2 a e =
    sum_CASE (decode_sum a)
    (λa. f1 a (FST (decode_pair e)))
    (λa. f2 a (SND (decode_pair e)))
End

Definition sum_def:
  sum c1 c2 = <| world := c1.world ∪ c2.world;
                 agent := IMAGE encode_sum (IMAGE INL c1.agent ∪ IMAGE INR c2.agent);
                 env := IMAGE encode_pair (c1.env × c2.env);
                 eval := sum_eval c1.eval c2.eval |>
End

Theorem wf_sum[simp]:
  wf c1 ∧ wf c2 ⇒ wf (sum c1 c2)
Proof
  rw[wf_def]
  \\ fs[sum_def]
  \\ fs[sum_eval_def]
QED

Theorem sum_in_chu_objects[simp]:
  c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ⇒ sum c1 c2 ∈ chu_objects w
Proof
  rw[chu_objects_def] \\ rw[sum_def]
QED

Definition comm_sum_def:
  comm_sum = <|
    map_agent := λs.
        sum_CASE (decode_sum s)
          (λa. encode_sum (INR a))
          (λa. encode_sum (INL a));
    map_env := λp.
      let (e1, e2) = decode_pair p in encode_pair (e2, e1)
  |>
End

Theorem comm_sum_is_chu_morphism[simp]:
  is_chu_morphism (sum c1 c2) (sum c2 c1)
    (mk_chu_morphism (sum c1 c2) (sum c2 c1) comm_sum).map
Proof
  simp[is_chu_morphism_def, mk_chu_morphism_def]
  \\ simp[restrict_def]
  \\ simp[sum_def, comm_sum_def, EXISTS_PROD]
  \\ rw[] \\ fs[]
  \\ simp[sum_eval_def]
QED

Theorem sum_comm:
  c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ⇒
  sum c1 c2 ≅ sum c2 c1 -: chu w
Proof
  rw[iso_objs_def]
  \\ qexists_tac`mk_chu_morphism (sum c1 c2) (sum c2 c1) comm_sum`
  \\ qexists_tac`mk_chu_morphism (sum c2 c1) (sum c1 c2) comm_sum`
  \\ simp[iso_pair_between_objs_def]
  \\ qmatch_goalsub_abbrev_tac`f <≃> g -: _`
  \\ simp[iso_pair_def]
  \\ conj_asm1_tac >- simp[Abbr`f`, Abbr`g`, composable_in_def, pre_chu_def]
  \\ `g ≈> f -: chu w` by simp[Abbr`f`, Abbr`g`, composable_in_def, pre_chu_def]
  \\ simp[compose_in_thm]
  \\ DEP_REWRITE_TAC[compose_thm]
  \\ conj_tac >- fs[composable_in_def]
  \\ simp[morphism_component_equality]
  \\ `g.dom ∈ chu_objects w ∧ f.cod ∈ chu_objects w` by simp[Abbr`f`, Abbr`g`]
  \\ `g.cod ∈ chu_objects w ∧ f.dom ∈ chu_objects w` by simp[Abbr`f`, Abbr`g`]
  \\ simp[]
  \\ simp[pre_chu_def, chu_id_morphism_map_def]
  \\ simp[Abbr`f`, Abbr`g`, mk_chu_morphism_def]
  \\ simp[FUN_EQ_THM, restrict_def]
  \\ simp[comm_sum_def, sum_def, EXISTS_PROD]
  \\ rw[] \\ fs[]
QED

Definition assoc_sum_def:
  assoc_sum ltr =
    <| map_agent := λa.
         if ¬ltr ∧ (∃x. a = encode_sum (INL (encode_sum (INL x)))) then
           OUTL (decode_sum a)
         else if ¬ltr ∧ (∃x. a = encode_sum (INL (encode_sum (INR x)))) then
           encode_sum (INR (encode_sum (INL (OUTR (decode_sum (OUTL (decode_sum a)))))))
         else if ltr ∧ (∃x. a = encode_sum (INR (encode_sum (INL x)))) then
           encode_sum (INL (encode_sum (INR (OUTL (decode_sum (OUTR (decode_sum a)))))))
         else if ltr ∧ (∃x. a = encode_sum (INR (encode_sum (INR x)))) then
           OUTR (decode_sum a)
         else if ltr ∧ (∃x. a = encode_sum (INL x)) then
           encode_sum (INL a)
         else encode_sum (INR a);
       map_env := λa.
         if ¬ltr ∧ (∃a1 a2 a3. a = encode_pair (a1, encode_pair (a2, a3))) then
           let (a1, p) = decode_pair a in
           let (a2, a3) = decode_pair p in
           encode_pair (encode_pair (a1, a2), a3)
         else
           let (p, a3) = decode_pair a in
           let (a1, a2) = decode_pair p in
           encode_pair (a1, encode_pair (a2, a3))
         |>
End

Theorem assoc_sum_is_chu_morphism[simp]:
  c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ∧ c3 ∈ chu_objects w ⇒
  is_chu_morphism (sum c1 (sum c2 c3)) (sum (sum c1 c2) c3)
    (mk_chu_morphism (sum c1 (sum c2 c3)) (sum (sum c1 c2) c3) (assoc_sum T)).map ∧
  is_chu_morphism (sum (sum c1 c2) c3) (sum c1 (sum c2 c3))
    (mk_chu_morphism (sum (sum c1 c2) c3) (sum c1 (sum c2 c3)) (assoc_sum F)).map
Proof
  simp[is_chu_morphism_def]
  \\ rw[mk_chu_morphism_def, sum_def, PULL_EXISTS, FORALL_PROD, EXISTS_PROD]
  \\ rw[restrict_def, assoc_sum_def, sum_eval_def]
QED

Theorem sum_assoc:
  c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ∧ c3 ∈ chu_objects w ⇒
  sum c1 (sum c2 c3) ≅ sum (sum c1 c2) c3 -: chu w
Proof
  rw[iso_objs_def]
  \\ qexists_tac`mk_chu_morphism (sum c1 (sum c2 c3)) (sum (sum c1 c2) c3) (assoc_sum T)`
  \\ qexists_tac`mk_chu_morphism (sum (sum c1 c2) c3) (sum c1 (sum c2 c3)) (assoc_sum F)`
  \\ simp[iso_pair_between_objs_def]
  \\ qmatch_goalsub_abbrev_tac`f <≃> g -: _`
  \\ simp[iso_pair_def]
  \\ conj_asm1_tac >- (
    simp[Abbr`f`, Abbr`g`, composable_in_def, pre_chu_def]
    \\ match_mp_tac assoc_sum_is_chu_morphism (* not sure why simp does not get this *)
    \\ simp[] )
  \\ `g ≈> f -: chu w` by (
    simp[Abbr`f`, Abbr`g`, composable_in_def, pre_chu_def]
    \\ match_mp_tac (ONCE_REWRITE_RULE[CONJ_COMM]assoc_sum_is_chu_morphism)
    \\ simp[] )
  \\ simp[compose_in_thm]
  \\ DEP_REWRITE_TAC[compose_thm]
  \\ conj_tac >- fs[composable_in_def]
  \\ simp[morphism_component_equality]
  \\ `g.dom ∈ chu_objects w ∧ f.cod ∈ chu_objects w` by simp[Abbr`f`, Abbr`g`]
  \\ `g.cod ∈ chu_objects w ∧ f.dom ∈ chu_objects w` by simp[Abbr`f`, Abbr`g`]
  \\ simp[]
  \\ simp[pre_chu_def]
  \\ simp[Abbr`f`, Abbr`g`]
  \\ simp[mk_chu_morphism_def]
  \\ simp[chu_id_morphism_map_def, restrict_def]
  \\ simp[sum_def, assoc_sum_def, FUN_EQ_THM, EXISTS_PROD]
  \\ rw[] \\ fs[]
QED

Definition cf0_def:
  cf0 w = <| world := w; agent := ∅; env := {""}; eval := K (K (CHOICE w)) |>
End

Theorem wf_cf0[simp]:
  wf (cf0 w)
Proof
  rw[wf_def, cf0_def]
QED

Theorem cf0_in_chu_objects[simp]:
  cf0 w ∈ chu_objects w
Proof
  rw[chu_objects_def] \\ rw[cf0_def]
QED

Definition remove_cf0_def:
  remove_cf0 onl = <|
    map_agent := λa.(if onl then OUTR else OUTL) (decode_sum a);
    map_env := λe. encode_pair (if onl then ("", e) else (e, "")) |>
End

Definition add_cf0_def:
  add_cf0 onl = <|
    map_agent := λa. encode_sum ((if onl then INR else INL) a);
    map_env := λe. (if onl then SND else FST) (decode_pair e) |>
End

Theorem add_remove_cf0_is_chu_morphism[simp]:
  c ∈ chu_objects w ⇒
  is_chu_morphism c (sum c (cf0 w)) (mk_chu_morphism c (sum c (cf0 w)) (add_cf0 F)).map ∧
  is_chu_morphism c (sum (cf0 w) c) (mk_chu_morphism c (sum (cf0 w) c) (add_cf0 T)).map ∧
  is_chu_morphism (sum c (cf0 w)) c (mk_chu_morphism (sum c (cf0 w)) c (remove_cf0 F)).map ∧
  is_chu_morphism (sum (cf0 w) c) c (mk_chu_morphism (sum (cf0 w) c) c (remove_cf0 T)).map
Proof
  rw[is_chu_morphism_def, mk_chu_morphism_def]
  \\ fs[restrict_def]
  \\ fs[sum_def, FORALL_PROD, EXISTS_PROD, cf0_def, add_cf0_def, remove_cf0_def]
  \\ rw[] \\ fs[] \\ rw[sum_eval_def]
QED

Theorem sum_cf0:
  c ∈ chu_objects w ⇒
  sum c (cf0 w) ≅ c -: chu w ∧
  sum (cf0 w) c ≅ c -: chu w
Proof
  simp[iso_objs_def] \\ strip_tac
  \\ conj_tac
  THENL [
    qexists_tac`mk_chu_morphism (sum c (cf0 w)) c (remove_cf0 F)`
    \\ qexists_tac`mk_chu_morphism c (sum c (cf0 w)) (add_cf0 F)`,
    qexists_tac`mk_chu_morphism (sum (cf0 w) c) c (remove_cf0 T)`
    \\ qexists_tac`mk_chu_morphism c (sum (cf0 w) c) (add_cf0 T)`
  ]
  \\ simp[iso_pair_between_objs_def]
  \\ qmatch_goalsub_abbrev_tac`f <≃> g -: _`
  \\ simp[iso_pair_def]
  \\ (conj_asm1_tac >- ( simp[Abbr`f`, Abbr`g`, composable_in_def, pre_chu_def]))
  \\ `g ≈> f -: chu w` by ( simp[Abbr`f`, Abbr`g`, composable_in_def, pre_chu_def])
  \\ simp[compose_in_thm]
  \\ DEP_REWRITE_TAC[compose_thm]
  \\ (conj_tac >- fs[composable_in_def])
  \\ simp[morphism_component_equality]
  \\ `g.dom ∈ chu_objects w ∧ f.cod ∈ chu_objects w` by simp[Abbr`f`, Abbr`g`]
  \\ `g.cod ∈ chu_objects w ∧ f.dom ∈ chu_objects w` by simp[Abbr`f`, Abbr`g`]
  \\ simp[]
  \\ simp[pre_chu_def]
  \\ simp[Abbr`f`, Abbr`g`, mk_chu_morphism_def, chu_id_morphism_map_def]
  \\ rw[restrict_def, remove_cf0_def, add_cf0_def, FUN_EQ_THM]
  \\ fs[sum_def, cf0_def, EXISTS_PROD] \\ rw[] \\ fs[]
QED

Theorem is_initial_cf0[simp]:
  is_initial (chu w) (cf0 w)
Proof
  rw[is_initial_thm]
  \\ simp[EXISTS_UNIQUE_THM]
  \\ conj_tac
  >- (
    qexists_tac`mk_chu_morphism (cf0 w) y <| map_env := K "" |>`
    \\ simp[maps_to_in_def, pre_chu_def]
    \\ simp[mk_chu_morphism_def]
    \\ simp[is_chu_morphism_def]
    \\ simp[cf0_def, restrict_def] )
  \\ rw[]
  \\ simp[morphism_component_equality]
  \\ fs[maps_to_in_def]
  \\ fs[pre_chu_def, is_chu_morphism_def]
  \\ simp[chu_morphism_map_component_equality]
  \\ fs[cf0_def, extensional_def]
  \\ simp[FUN_EQ_THM]
  \\ metis_tac[]
QED

Theorem has_binary_products_chu_op:
  has_binary_products (chu w)°
Proof
  simp[has_binary_products_thm, is_binary_product_thm]
  \\ rpt strip_tac
  \\ qexists_tac`sum a b`
  \\ qexists_tac`<| dom := (sum a b); cod := a; map :=
      <| map_agent := restrict (encode_sum o INL) a.agent;
         map_env := restrict (FST o decode_pair) (sum a b).env |> |>`
  \\ qexists_tac`<| dom := (sum a b); cod := b; map :=
      <| map_agent := restrict (encode_sum o INR) b.agent;
         map_env := restrict (SND o decode_pair) (sum a b).env |> |>`
  \\ qmatch_goalsub_abbrev_tac`p1 ° :- a → _ -: _`
  \\ qmatch_goalsub_abbrev_tac`p2 ° :- b → _ -: _`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_def, pre_chu_def]
    \\ simp[is_chu_morphism_def]
    \\ simp[Abbr`p1`]
    \\ simp[sum_def, EXISTS_PROD, PULL_EXISTS]
    \\ simp[restrict_def]
    \\ simp[sum_eval_def] )
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_def, pre_chu_def]
    \\ simp[is_chu_morphism_def]
    \\ simp[Abbr`p2`]
    \\ simp[sum_def, EXISTS_PROD, PULL_EXISTS]
    \\ simp[restrict_def]
    \\ simp[sum_eval_def] )
  \\ qx_gen_tac`c`
  \\ qx_genl_tac[`m1`,`m2`]
  \\ strip_tac
  \\ imp_res_tac maps_to_obj \\ fs[]
  \\ simp[EXISTS_UNIQUE_THM]
  \\ conj_tac
  >- (
    qexists_tac`<| dom := c; cod := sum a b; map :=
      <| map_agent := restrict (λs. sum_CASE (decode_sum s) m1.map.map_agent m2.map.map_agent)
                        (sum a b).agent;
         map_env := restrict (λe. encode_pair (m1.map.map_env e, m2.map.map_env e)) c.env |> |>`
    \\ qmatch_goalsub_abbrev_tac`op_mor m`
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_def]
      \\ simp[pre_chu_def]
      \\ simp[Abbr`m`]
      \\ simp[is_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[sum_def, EXISTS_PROD, PULL_EXISTS]
      \\ simp[sum_eval_def]
      \\ fs[maps_to_in_def, pre_chu_def, is_chu_morphism_def, restrict_def]
      \\ rw[] \\ rw[] \\ fs[] )
    \\ DEP_REWRITE_TAC[compose_in_thm]
    \\ conj_tac >- ( fs[maps_to_in_def, composable_in_def] )
    \\ DEP_REWRITE_TAC[compose_thm]
    \\ conj_tac >- ( fs[maps_to_in_def, composable_in_def] )
    \\ simp[morphism_component_equality]
    \\ fs[maps_to_in_def]
    \\ DEP_REWRITE_TAC[chu_comp]
    \\ simp[composable_in_def]
    \\ simp[pre_chu_def]
    \\ simp[chu_morphism_map_component_equality]
    \\ simp[Abbr`m`, restrict_def]
    \\ simp[Abbr`p1`, Abbr`p2`]
    \\ simp[sum_def, restrict_def, FUN_EQ_THM]
    \\ fs[pre_chu_def, is_chu_morphism_def, extensional_def]
    \\ rw[] )
  \\ qx_genl_tac[`p`,`q`]
  \\ strip_tac
  \\ simp[morphism_component_equality]
  \\ fs[maps_to_in_def]
  \\ simp[chu_morphism_map_component_equality]
  \\ rpt(qpat_x_assum`_ o _ -: _ = _`mp_tac)
  \\ DEP_REWRITE_TAC[compose_in_thm]
  \\ simp[composable_in_def]
  \\ disch_then (SUBST1_TAC o GSYM)
  \\ disch_then (SUBST1_TAC o GSYM)
  \\ simp[pre_chu_def]
  \\ simp[Abbr`p1`, Abbr`p2`]
  \\ simp[FUN_EQ_THM, restrict_def]
  \\ strip_tac
  \\ strip_tac
  \\ fs[pre_chu_def, is_chu_morphism_def, extensional_def, restrict_def]
  \\ fs[sum_def, EXISTS_PROD, PULL_EXISTS]
  \\ conj_tac
  >- (
    qx_gen_tac`z`
    \\ qpat_x_assum`∀z. _ ⇒ p.map.map_agent z = ARB`(qspec_then`z`mp_tac)
    \\ qpat_x_assum`∀z. _ ⇒ q.map.map_agent z = ARB`(qspec_then`z`mp_tac)
    \\ qmatch_goalsub_abbrev_tac`cnd ⇒ (_ = _)`
    \\ Cases_on`cnd = T` \\ fs[Abbr`cnd`]
    \\ metis_tac[] )
  >- (
    qx_gen_tac`z`
    \\ qpat_x_assum`∀z. _ ⇒ p.map.map_env z = ARB`(qspec_then`z`mp_tac)
    \\ qpat_x_assum`∀z. _ ⇒ q.map.map_env z = ARB`(qspec_then`z`mp_tac)
    \\ qmatch_goalsub_abbrev_tac`cnd ⇒ (_ = _)`
    \\ Cases_on`cnd = T` \\ fs[Abbr`cnd`]
    \\ first_x_assum(qspec_then`z`mp_tac) \\ simp[]
    \\ qpat_x_assum`∀x. (COND (x ∈ c.env) _ _) = _`(qspec_then`z`mp_tac) \\ simp[]
    \\ first_x_assum(fn th =>
         qspec_then`z`mp_tac th \\ simp[] \\ disch_then(qx_choose_then`_0`strip_assume_tac))
    \\ first_x_assum(fn th =>
         qspec_then`z`mp_tac th \\ simp[] \\ disch_then(qx_choose_then`_1`strip_assume_tac))
    \\ simp[] )
QED

Definition cfT_def:
  cfT w = swap (cf0 w)
End

Theorem cfT_in_chu_objects[simp]:
  cfT w ∈ chu_objects w
Proof
  rw[cfT_def]
QED

Theorem cfT_agent_env:
  (cfT w).agent = {""} ∧
  (cfT w).env = ∅
Proof
  rw[cfT_def, swap_def, cf0_def]
QED

Theorem cfT_swap_cf0:
  cfT w = swap_functor w @@ (cf0 w) ∧
  cfT w = op_swap_functor w @@ (cf0 w)
Proof
  rw[cfT_def]
QED

Theorem cf0_swap_cfT:
  cf0 w = (swap_functor w) @@ (cfT w) ∧
  cf0 w = (op_swap_functor w) @@ (cfT w)
Proof
  rw[cfT_def]
QED

Theorem is_terminal_cfT:
  is_terminal (chu w) (cfT w)
Proof
  rewrite_tac[CONJUNCT2 cfT_swap_cf0]
  \\ match_mp_tac is_terminal_cat_iso
  \\ qexists_tac`(chu w) °`
  \\ mp_tac cat_iso_pair_swap_functor
  \\ simp[cat_iso_def]
  \\ mp_tac is_initial_cf0
  \\ rewrite_tac[is_initial_def]
  \\ simp[]
  \\ simp[Once cat_iso_pair_sym]
  \\ rw[] >- metis_tac[]
  \\ simp[op_swap_functor_def]
QED

Definition prod_def:
  prod c1 c2 =  <| world := c1.world ∪ c2.world;
                   agent := IMAGE encode_pair (c1.agent × c2.agent);
                   env := IMAGE encode_sum (IMAGE INL c1.env ∪ IMAGE INR c2.env);
                   eval := flip (sum_eval (flip c1.eval) (flip c2.eval)) |>
End

Theorem swap_sum_prod:
  swap (sum (swap c) (swap d)) = prod c d
Proof
  rw[cf_component_equality]
  \\ rw[prod_def, sum_def]
  \\ rw[swap_def, FUN_EQ_THM]
QED

Theorem swap_prod_sum:
  swap (prod (swap c) (swap d)) = sum c d
Proof
  rw[cf_component_equality]
  \\ rw[prod_def, sum_def]
  \\ rw[swap_def, FUN_EQ_THM]
  \\ srw_tac[boolSimps.ETA_ss][C_DEF]
QED

Theorem has_binary_products_chu:
  has_binary_products (chu w)
Proof
  assume_tac has_binary_products_chu_op
  \\ fs[has_binary_products_thm]
  \\ fs[is_binary_product_thm]
  \\ rpt gen_tac \\ strip_tac
  \\ first_x_assum(qspecl_then[`swap a`,`swap b`]mp_tac)
  \\ simp[] \\ strip_tac
  \\ qexists_tac`swap ab`
  \\ qexists_tac`(op_swap_functor w) ## $π1`
  \\ qexists_tac`(op_swap_functor w) ## $π2`
  \\ rewrite_tac[CONJ_ASSOC]
  \\ conj_asm1_tac
  >- (
    conj_tac
    \\ match_mp_tac morf_maps_to \\ simp[]
    \\ simp[Once op_swap_functor_def]
    \\ simp[Once op_swap_functor_def]
    \\ imp_res_tac maps_to_obj
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ fs[] )
  \\ rpt gen_tac \\ strip_tac
  \\ first_x_assum(qspecl_then[`swap p`,`swap_functor w ## p1`,`swap_functor w ## p2`]mp_tac)
  \\ impl_keep_tac
  >- (
    conj_tac
    \\ rewrite_tac[GSYM op_cat_maps_to_in]
    \\ match_mp_tac morf_maps_to \\ simp[]
    \\ simp[Once swap_functor_def]
    \\ simp[Once swap_functor_def]
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ imp_res_tac maps_to_obj
    \\ fs[] )
  \\ simp[GSYM CONJ_ASSOC]
  \\ Ho_Rewrite.REWRITE_TAC[EXISTS_UNIQUE_THM]
  \\ strip_tac
  \\ conj_tac
  >- (
    first_x_assum(qspec_then`ARB`kall_tac)
    \\ qexists_tac`op_swap_functor w ## m`
    \\ conj_asm1_tac
    >- (
      match_mp_tac morf_maps_to \\ simp[]
      \\ simp[Once op_swap_functor_def]
      \\ simp[Once op_swap_functor_def]
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ imp_res_tac maps_to_obj
      \\ fs[] )
    \\ qmatch_goalsub_abbrev_tac`(G ## g) o (G ## f) -: chu w`
    \\ qspecl_then[`G`,`op_cat(chu w)`]mp_tac morf_comp
    \\ disch_then(fn th=> DEP_REWRITE_TAC[GSYM th])
    \\ simp[Abbr`G`,Abbr`f`,Abbr`g`]
    \\ simp[Once op_swap_functor_def]
    \\ simp[Once op_swap_functor_def]
    \\ conj_tac
    >- (
      conj_tac
      \\ match_mp_tac maps_to_composable
      \\ metis_tac[] )
    \\ fs[]
    \\ metis_tac[swap_functor_morf, maps_to_in_def, chu_mor,
                 op_cat_maps_to_in, swap_morphism_idem])
  \\ qx_genl_tac[`s`,`t`]
  \\ strip_tac
  \\ `swap_functor w ## s = swap_functor w ## t` suffices_by (
    metis_tac[swap_functor_morf, maps_to_in_def, chu_mor, swap_morphism_inj] )
  \\ first_x_assum match_mp_tac
  \\ qmatch_goalsub_abbrev_tac`G ## s`
  \\ CONV_TAC(markerLib.move_conj_left(Lib.mem"t" o List.map (#1 o dest_var) o free_vars))
  \\ simp[GSYM CONJ_ASSOC]
  \\ simp[Once CONJ_ASSOC]
  \\ conj_asm1_tac
  >- (
    conj_tac
    \\ once_rewrite_tac[GSYM op_cat_maps_to_in]
    \\ match_mp_tac morf_maps_to \\ simp[Abbr`G`]
    \\ simp[Once swap_functor_def]
    \\ simp[Once swap_functor_def]
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ imp_res_tac maps_to_obj \\ fs[] )
  \\ cheat
QED

val _ = export_theory();