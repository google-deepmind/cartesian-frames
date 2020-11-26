open HolKernel boolLib bossLib Parse cf0Theory categoryTheory functorTheory

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
  c ∈ chu_objects w ⇒ swap c ∈ chu_objects w
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
  is_chu_morphism c1 c2 m ⇒
  is_chu_morphism (swap c2) (swap c1) (swap_morphism_map m)
Proof
  rw[is_chu_morphism_def]
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

(*
Theorem cat_iso_pair_swap_functor:
  cat_iso_pair (swap_functor w) (swap_functor w)°
*)

val _ = export_theory();
