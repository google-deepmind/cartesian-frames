open HolKernel boolLib bossLib pred_setTheory Parse

val _ = new_theory"cf0";

(* Cartesian Frames *)

Datatype:
  cf = <| agent: 'a set; env: 'e set; world: 'w set; eval: 'a -> 'e -> 'w |>
End

Definition wf_def:
  wf c ⇔ ∀a e. a ∈ c.agent ∧ e ∈ c.env ⇒ c.eval a e ∈ c.world
End

Definition image_def:
  image c = { w | w ∈ c.world ∧ ∃a e. a ∈ c.agent ∧ e ∈ c.env ∧ c.eval a e = w }
End

(* Initial definition of controllables *)

Definition ensure_def:
  ensure c = { s | s ⊆ c.world ∧ ∃a. a ∈ c.agent ∧ ∀e. e ∈ c.env ⇒ c.eval a e ∈ s }
End

Definition prevent_def:
  prevent c = { s | s ⊆ c.world ∧ ∃a. a ∈ c.agent ∧ ∀e. e ∈ c.env ⇒ c.eval a e ∉ s }
End

Definition ctrl_def:
  ctrl c = ensure c ∩ prevent c
End

Theorem ensure_empty_agent:
  c.agent = ∅ ⇒ (ensure c = {})
Proof
  rw[ensure_def]
QED

Theorem ctrl_closure:
  c.world = c'.world ∧ c.agent ⊆ c'.agent ∧ c'.env ⊆ c.env ∧
  (∀a e. a ∈ c.agent ∧ e ∈ c'.env ⇒ c'.eval a e = c.eval a e) ⇒
  ensure c ⊆ ensure c' ∧ prevent c ⊆ prevent c' ∧ ctrl c ⊆ ctrl c'
Proof
  rw[ensure_def, prevent_def, ctrl_def, SUBSET_DEF] \\ metis_tac[]
QED

Theorem ensure_superset:
  s1 ⊆ s2 ∧ s2 ⊆ c.world ∧ s1 ∈ ensure c ⇒ s2 ∈ ensure c
Proof
  rw[ensure_def, SUBSET_DEF] \\ metis_tac[]
QED

Theorem prevent_subset:
  s1 ⊆ s2 ∧ s2 ⊆ c.world ∧ s2 ∈ prevent c ⇒ s2 ∈ prevent c
Proof
  rw[prevent_def, SUBSET_DEF] \\ metis_tac[]
QED

Definition sup_closure_def:
  sup_closure u sos = { s | s ⊆ u ∧ ∃t. t ∈ sos ∧ t ⊆ s }
End

Definition sub_closure_def:
  sub_closure u sos = { s | s ⊆ u ∧ ∃t. t ∈ sos ∧ s ⊆ t }
End

(* Initial definition of observables *)

Definition ifs_def:
  ifs c s a0 a1 =
  { a | a ∈ c.agent ∧ ∀e. e ∈ c.env ⇒
    (c.eval a e ∈ s ⇒ c.eval a e = c.eval a0 e) ∧
    (c.eval a e ∉ s ⇒ c.eval a e = c.eval a1 e) }
End

Theorem ifs_compl:
  s ⊆ c.world ∧ wf c⇒
    ifs c s a0 a1 = ifs c (c.world DIFF s) a1 a0
Proof
  rw[ifs_def, wf_def]
  \\ fs[SUBSET_DEF]
  \\ rw[Once EXTENSION]
  \\ metis_tac[]
QED

Definition obs_def:
  obs c = { s | s ⊆ c.world ∧ ∀a0 a1. a0 ∈ c.agent ∧ a1 ∈ c.agent ⇒
    ∃a. a ∈ c.agent ∧ a ∈ ifs c s a0 a1 }
End

Theorem obs_compl:
  wf c ∧ s ∈ obs c ⇒ c.world DIFF s ∈ obs c
Proof
  rw[obs_def] \\ rw[GSYM ifs_compl]
QED

Theorem obs_union:
  s ∈ obs c ∧ t ∈ obs c ⇒ s ∪ t ∈ obs c
Proof
  rw[obs_def]
  \\ `∃a2. a2 ∈ c.agent ∧ a2 ∈ ifs c s a0 a1` by metis_tac[]
  \\ `∃a3. a3 ∈ c.agent ∧ a3 ∈ ifs c t a0 a2` by metis_tac[]
  \\ qexists_tac`a3` \\ rw[]
  \\ fs[ifs_def]
  \\ metis_tac[]
QED

Theorem obs_inter:
  wf c ∧ s ∈ obs c ∧ t ∈ obs c ⇒ s ∩ t ∈ obs c
Proof
  strip_tac
  \\ imp_res_tac obs_compl
  \\ `s ⊆ c.world ∧ t ⊆ c.world` by fs[obs_def]
  \\ `s ∩ t = c.world DIFF ((c.world DIFF s) ∪ (c.world DIFF t))` by (
    rw[EXTENSION] \\ fs[SUBSET_DEF] \\ metis_tac[] )
  \\ pop_assum SUBST1_TAC
  \\ match_mp_tac obs_compl \\ fs[]
  \\ match_mp_tac obs_union \\ fs[]
QED

Theorem obs_closure:
  c'.env ⊆ c.env ∧ c'.world = c.world ∧ c'.agent = c.agent ∧
  (∀a e. a ∈ c.agent ∧ e ∈ c'.env ⇒ c'.eval a e = c.eval a e) ⇒
  obs c ⊆ obs c'
Proof
  rw[obs_def, SUBSET_DEF]
  \\ first_x_assum (qspecl_then[`a0`,`a1`]mp_tac)
  \\ rw[]
  \\ fs[ifs_def]
  \\ metis_tac[]
QED

val _ = export_theory();
