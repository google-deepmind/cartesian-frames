open HolKernel boolLib bossLib Parse cf0Theory categoryTheory functorTheory dep_rewrite

val _ = new_theory"cf1";

Datatype:
  chu_morphism_map = <| map_agent: 'a -> 'b; map_env: 'f -> 'e |>
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

val _ = type_abbrev_pp("chu_morphism",
  ``:(('a, 'e, 'w) cf, ('b, 'f, 'w) cf, ('a, 'b, 'e, 'f) chu_morphism_map) morphism``);

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

Theorem iso_pair_between_cats_chu_op =
  iso_pair_between_cats_def
  |> CONV_RULE SWAP_FORALL_CONV
  |> Q.ISPECL[`swap_functor w`, `chu w`]
  |> Q.ISPEC`op_swap_functor w`
  |> Q.ISPEC `op_cat (chu w)`
  |> REWRITE_RULE[cat_iso_pair_swap_functor, maps_to_def]
  |> CONV_RULE(RAND_CONV(SIMP_CONV(srw_ss())[swap_functor_def]))
  |> EQT_ELIM

val tm = iso_pair_between_cats_chu_op |> concl
val (func, args) = strip_comb tm
val [ctm, ftm, gtm, cotm] = args
val varf = mk_var("f", type_of ftm)
val varg = mk_var("g", type_of gtm)
val tm' = list_mk_exists([varf, varg],
  list_mk_comb(func, [ctm, varf, varg, cotm]))

Theorem iso_cats_chu_op =
  iso_cats_def |> ISPECL[ctm, cotm]
  |> REWRITE_RULE[prove(tm', metis_tac[iso_pair_between_cats_chu_op])]

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
  \\ `e = op_mor (swap_morphism e)`
  by (
    simp[morphism_component_equality]
    swap_def
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

val _ = export_theory();
