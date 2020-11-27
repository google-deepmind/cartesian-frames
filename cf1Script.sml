open HolKernel boolLib bossLib Parse cf0Theory categoryTheory functorTheory
     dep_rewrite sumTheory pairTheory pred_setTheory listTheory rich_listTheory ASCIInumbersTheory

val _ = new_theory"cf1";

Datatype:
  chu_morphism_map = <| map_agent: act -> act; map_env: act -> act |>
End

val chu_morphism_map_component_equality = theorem"chu_morphism_map_component_equality";

Definition is_chu_morphism_def:
  is_chu_morphism c1 c2 m ⇔
    (∀e. e ∈ c2.env ⇒ m.map_env e ∈ c1.env) ∧
    (∀a. a ∈ c1.agent ⇒ m.map_agent a ∈ c2.agent) ∧
    (∀a f. a ∈ c1.agent ∧ f ∈ c2.env ⇒
       c1.eval a (m.map_env f) = c2.eval (m.map_agent a) f)
End

Theorem is_chu_morphism_id[simp]:
  is_chu_morphism c c <| map_agent := I; map_env := I |>
Proof
  rw[is_chu_morphism_def]
QED

Definition chu_objects_def:
  chu_objects w = { c | wf c ∧ c.world = w }
End

val _ = type_abbrev_pp("chu_morphism", ``:('w cf, 'w cf, chu_morphism_map) morphism``);

Definition pre_chu_def:
  pre_chu w =
    <| obj := chu_objects w;
       mor := { m | m.dom ∈ chu_objects w ∧ m.cod ∈ chu_objects w ∧
                    is_chu_morphism m.dom m.cod m.map };
       id_map := K <| map_agent := I; map_env := I |>;
       comp := λm1 m2. <| map_agent := m2.map.map_agent o m1.map.map_agent;
                          map_env := m1.map.map_env o m2.map.map_env |>
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
    \\ simp[morphism_component_equality, chu_morphism_map_component_equality])
  \\ conj_tac >- (
    simp[pre_chu_def, id_in_def, restrict_def, compose_in_def, composable_in_def]
    \\ simp[morphism_component_equality, chu_morphism_map_component_equality])
  \\ conj_tac >- (
    simp[composable_in_def, compose_in_def, restrict_def]
    \\ rw[pre_chu_def]
    \\ `F` suffices_by rw[]
    \\ qpat_x_assum`¬_`mp_tac
    \\ fs[is_chu_morphism_def])
  \\ rw[maps_to_in_def, compose_in_def, restrict_def, composable_in_def]
  \\ fs[pre_chu_def, is_chu_morphism_def]
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
  (chu w).id_map = restrict (K <| map_agent := I; map_env := I |>) (chu_objects w)
Proof
  rw[chu_def, pre_chu_def, mk_cat_def]
QED

Definition swap_def:
  swap c = <| world := c.world; agent := c.env; env := c.agent;
              eval := λa e. c.eval e a |>
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
  \\ srw_tac[boolSimps.ETA_ss][]
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

Theorem swap_morphism_id:
  c ∈ chu_objects w ⇒
  swap_morphism (id c -: chu w) = id (swap c) -: chu w
Proof
  rw[id_in_def, restrict_def, swap_morphism_def, morphism_component_equality] \\ rfs[]
  \\ rw[swap_morphism_map_def, chu_id_map]
  \\ rw[chu_morphism_map_component_equality, restrict_def]
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
  c ∈ chu_objects w ⇒ (swap_functor w) @@ c = swap c
Proof
  rw[swap_functor_def]
  \\ rw[objf_def, morf_def]
  \\ SELECT_ELIM_TAC
  \\ conj_tac >- metis_tac[swap_morphism_id, swap_in_chu_objects]
  \\ simp[swap_morphism_id]
  \\ rw[]
  \\ qspec_then`chu w`match_mp_tac id_inj
  \\ simp[]
QED

Theorem swap_functor_idem[simp]:
  c ∈ chu_objects w ⇒ (swap_functor w) @@ ((swap_functor w) @@ c) = c
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
      if (∃a. s = encode_sum a) then
        sum_CASE (decode_sum s)
          (λa. encode_sum (INR a))
          (λa. encode_sum (INL a))
      else s;
    map_env := λp.
      if (∃e1 e2. p = encode_pair (e1, e2))
      then let (e1, e2) = decode_pair p in encode_pair (e2, e1)
      else p
  |>
End

Theorem comm_sum_is_chu_morphism[simp]:
  is_chu_morphism (sum c1 c2) (sum c2 c1) comm_sum
Proof
  simp[is_chu_morphism_def]
  \\ conj_tac
  >- (
    simp[sum_def, comm_sum_def, EXISTS_PROD]
    \\ gen_tac \\ strip_tac
    \\ simp[] \\ metis_tac[] )
  \\ conj_tac
  >- (
    simp[sum_def, comm_sum_def]
    \\ gen_tac \\ strip_tac \\ simp[]
    \\ metis_tac[])
  \\ simp[sum_def, comm_sum_def, EXISTS_PROD]
  \\ rw[] \\ fs[] \\ rw[sum_eval_def]
  \\ TRY (qmatch_goalsub_rename_tac`sum_CASE a` \\ CASE_TAC \\ fs[])
  \\ metis_tac[PAIR_FST_SND_EQ, FST, SND, decode_encode_pair, decode_encode_sum,
               INR_INL_11, sum_distinct]
QED

Theorem sum_comm:
  c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ⇒
  sum c1 c2 ≅ sum c2 c1 -: chu w
Proof
  rw[iso_objs_def]
  \\ qexists_tac`<| dom := sum c1 c2; cod := sum c2 c1; map := comm_sum |>`
  \\ qexists_tac`<| dom := sum c2 c1; cod := sum c1 c2; map := comm_sum |>`
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
  \\ simp[chu_id_map, restrict_def]
  \\ simp[pre_chu_def]
  \\ simp[Abbr`f`, Abbr`g`]
  \\ conj_tac
  >- (
    simp[comm_sum_def, FUN_EQ_THM]
    \\ rw[] \\ fs[] \\ pop_assum mp_tac
    \\ CASE_TAC \\ rw[] \\ rw[])
  \\ simp[comm_sum_def, FUN_EQ_THM]
  \\ qx_gen_tac`p`
  \\ Cases_on`∃e1 e2. p = encode_pair (e1, e2)` \\ simp[]
  \\ reverse CASE_TAC >- (fs[UNCURRY] \\ metis_tac[])
  \\ simp[UNCURRY] \\ fs[]
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
         else if ¬ltr ∧ (∃x. a = encode_sum (INR x)) then
           encode_sum (INR a)
         else if  (∃x. a = encode_sum (INL (encode_sum (INL x)))) then
           OUTL (decode_sum a)
         (*
         else if  (∃x. a = encode_sum (INL (encode_sum (INR x)))) then
           encode_sum (INR (encode_sum (INL (OUTR (decode_sum (OUTL (decode_sum a)))))))
         else if  (∃x. a = encode_sum (INR (encode_sum (INL x)))) then
           encode_sum (INL (encode_sum (INR (OUTL (decode_sum (OUTR (decode_sum a)))))))
         else if  (∃x. a = encode_sum (INR (encode_sum (INR x)))) then
           OUTR (decode_sum a)
         else if  (∃x. a = encode_sum (INL x)) then
           encode_sum (INL a)
         else if  (∃x. a = encode_sum (INR x)) then
           encode_sum (INR a)
         *)
         else if  (∃x. a = encode_sum (INL x)) then
           encode_sum (INR (OUTL (decode_sum a)))
         else if  (∃x. a = encode_sum (INR x)) then
           encode_sum (INL (OUTR (decode_sum a)))
         else a;
       map_env := λa.
         if ¬ltr ∧ (∃a1 a2 a3. a = encode_pair (a1, encode_pair (a2, a3))) then
           let (a1, p) = decode_pair a in
           let (a2, a3) = decode_pair p in
           encode_pair (encode_pair (a1, a2), a3)
         else if ltr ∧ (∃a1 a2 a3. a = encode_pair (encode_pair (a1, a2), a3)) then
           let (p, a3) = decode_pair a in
           let (a1, a2) = decode_pair p in
           encode_pair (a1, encode_pair (a2, a3))
         else if (∃a1 a2. a = encode_pair (a1, a2)) then
           let (a1, a2) = decode_pair a in (encode_pair (a2, a1))
         else a |>
End

Theorem assoc_sum_is_chu_morphism[simp]:
  c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ∧ c3 ∈ chu_objects w ⇒
  is_chu_morphism (sum c1 (sum c2 c3)) (sum (sum c1 c2) c3) (assoc_sum T) ∧
  is_chu_morphism (sum (sum c1 c2) c3) (sum c1 (sum c2 c3)) (assoc_sum F)
Proof
  simp[is_chu_morphism_def]
  \\ rw[sum_def, PULL_EXISTS, FORALL_PROD, EXISTS_PROD]
  \\ rw[assoc_sum_def, sum_eval_def]
QED

Theorem sum_assoc:
  c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ∧ c3 ∈ chu_objects w ⇒
  sum c1 (sum c2 c3) ≅ sum (sum c1 c2) c3 -: chu w
Proof
  rw[iso_objs_def]
  \\ qexists_tac`<| dom := sum c1 (sum c2 c3); cod := sum (sum c1 c2) c3; map := assoc_sum T |>`
  \\ qexists_tac`<| dom := sum (sum c1 c2) c3; cod := sum c1 (sum c2 c3); map := assoc_sum F |>`
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
  \\ simp[chu_id_map, restrict_def]
  \\ simp[pre_chu_def]
  \\ simp[Abbr`f`, Abbr`g`]
  \\ simp[GSYM CONJ_ASSOC]
  \\ simp[assoc_sum_def, FUN_EQ_THM]
  \\ rw[] \\ fs[] \\ pop_assum mp_tac
  \\ CASE_TAC \\ rw[] \\ rw[] \\ fs[]
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
    map_agent := λa.
      if ¬onl ∧ (∃x. a = encode_sum (INL x)) then OUTL (decode_sum a) else
      if onl ∧ (∃x. a = encode_sum (INR x)) then OUTR (decode_sum a) else
      a;
    map_env := λe.
      if ¬onl then encode_pair (e, "") else encode_pair ("", e) |>
End

Definition add_cf0_def:
  add_cf0 onl = <|
    map_agent := λa.
      if ¬onl then encode_sum (INL a) else encode_sum (INR a);
    map_env := λe.
      if ¬onl ∧ (∃x. e = encode_pair (x, "")) then FST (decode_pair e) else
      if onl ∧ (∃x. e = encode_pair ("", x)) then SND (decode_pair e) else
      e |>
End

Theorem add_remove_cf0_is_chu_morphism[simp]:
  c ∈ chu_objects w ⇒
  is_chu_morphism c (sum c (cf0 w)) (add_cf0 F) ∧
  is_chu_morphism c (sum (cf0 w) c) (add_cf0 T) ∧
  is_chu_morphism (sum c (cf0 w)) c (remove_cf0 F) ∧
  is_chu_morphism (sum (cf0 w) c) c (remove_cf0 T)
Proof
  rw[is_chu_morphism_def, sum_def, FORALL_PROD, EXISTS_PROD,
     cf0_def, add_cf0_def, remove_cf0_def]
  \\ rw[] \\ fs[] \\ rw[sum_eval_def]
QED

(*
Theorem sum_cf0:
  c ∈ chu_objects w ⇒
  sum c (cf0 w) ≅ c -: chu w ∧
  sum (cf0 w) c ≅ c -: chu w
Proof
  simp[iso_objs_def] \\ strip_tac
  \\ conj_tac
  >- (
    qexists_tac`<|dom:= sum c (cf0 w); cod := c; map := remove_cf0 F|>`
    \\ qexists_tac`<|dom:= c; cod := sum c (cf0 w); map := add_cf0 F|>`
    \\ simp[iso_pair_between_objs_def]
    \\ qmatch_goalsub_abbrev_tac`f <≃> g -: _`
    \\ simp[iso_pair_def]
    \\ conj_asm1_tac >- ( simp[Abbr`f`, Abbr`g`, composable_in_def, pre_chu_def])
    \\ `g ≈> f -: chu w` by ( simp[Abbr`f`, Abbr`g`, composable_in_def, pre_chu_def])
    \\ simp[compose_in_thm]
    \\ DEP_REWRITE_TAC[compose_thm]
    \\ conj_tac >- fs[composable_in_def]
    \\ simp[morphism_component_equality]
    \\ `g.dom ∈ chu_objects w ∧ f.cod ∈ chu_objects w` by simp[Abbr`f`, Abbr`g`]
    \\ `g.cod ∈ chu_objects w ∧ f.dom ∈ chu_objects w` by simp[Abbr`f`, Abbr`g`]
    \\ simp[]
    \\ simp[chu_id_map, restrict_def]
    \\ simp[pre_chu_def]
    \\ simp[Abbr`f`, Abbr`g`]
    \\ simp[GSYM CONJ_ASSOC]
    \\ conj_tac
    >- (simp[remove_cf0_def, add_cf0_def] \\ simp[FUN_EQ_THM] \\ rw[] \\ fs[])
    \\ conj_tac
    >- (simp[remove_cf0_def, add_cf0_def] \\ simp[FUN_EQ_THM] \\ rw[] \\ fs[])
    \\ conj_tac
    >- (simp[remove_cf0_def, add_cf0_def] \\ simp[FUN_EQ_THM] \\ rw[] \\ fs[])
*)

val _ = export_theory();
