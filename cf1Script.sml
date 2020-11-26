open HolKernel boolLib bossLib Parse cf0Theory categoryTheory

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

Theorem is_category_chu:
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

val _ = export_theory();
