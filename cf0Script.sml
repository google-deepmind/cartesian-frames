open HolKernel boolLib bossLib pred_setTheory Parse

val _ = new_theory"cf0";

(* Cartesian Frames *)
Datatype:
  cf = <| agent: 'a set; env: 'e set; world: 'w set; eval: 'a -> 'e -> 'w |>
End

Definition image_def:
  image c = { w | w ∈ c.world ∧ ∃a e. a ∈ c.agent ∧ e ∈ c.env ∧ c.eval a e = w }
End

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

(* Example *)

open stringTheory boolSimps

Definition runs_cf1_def:
  runs_cf1 = <| agent := { "u"; "n" }; env := { "r"; "s" };
                world := {"ur"; "us"; "nr"; "ns"};
                eval := λa e. a ++ e |>
End

Theorem sup_closure_example:
  sup_closure runs_cf1.world {{"ur"; "us"};{"nr";"ns"}} =
  {{"ur"; "us"};{"nr";"ns"};
   {"ur";"us";"nr"};{"ur";"us";"ns"};{"nr";"ns";"ur"};{"nr";"ns";"us"};
   runs_cf1.world}
Proof
  rw[SET_EQ_SUBSET]
  >- (
    rw[sup_closure_def, runs_cf1_def, SUBSET_DEF, SET_EQ_SUBSET]
    \\ fsrw_tac[DNF_ss][]
    \\ metis_tac[] )
  \\ rw[sup_closure_def]
  \\ srw_tac[DNF_ss][]
  \\ EVAL_TAC
QED

Theorem sub_closure_example:
  sub_closure runs_cf1.world {{"ur"; "us"};{"nr";"ns"}} =
  {{"ur"; "us"};{"nr";"ns"};
   {"ur"};{"us"};{"nr"};{"ns"};{}}
Proof
  rw[SET_EQ_SUBSET]
  \\ TRY (
    rw[sub_closure_def, runs_cf1_def]
    \\ fsrw_tac[DNF_ss][]
    \\ NO_TAC)
  \\ rw[sub_closure_def, runs_cf1_def, SUBSET_DEF]
  \\ spose_not_then strip_assume_tac \\ fs[EXTENSION]
  \\ metis_tac[]
QED

Theorem runs_ensure:
  ensure runs_cf1 = sup_closure runs_cf1.world {{"ur"; "us"}; {"nr"; "ns"}}
Proof
  rw[ensure_def, runs_cf1_def, sup_closure_example]
  \\ rw[SET_EQ_SUBSET, SUBSET_DEF]
  \\ fsrw_tac[DNF_ss][] \\ metis_tac[]
QED

Theorem runs_prevent:
  prevent runs_cf1 = sub_closure runs_cf1.world {{"ur";"us"};{"nr";"ns"}}
Proof
  rw[prevent_def, runs_cf1_def, sub_closure_example]
  \\ rw[SUBSET_DEF]
  \\ rw[Once EXTENSION]
  \\ EQ_TAC \\ rw[] \\ fsrw_tac[DNF_ss][]
  \\ spose_not_then strip_assume_tac
  \\ fsrw_tac[DNF_ss][EXTENSION]
  >- PROVE_TAC[]
  \\ metis_tac[]
QED

(* morphisms between Cartesian Frames *)

val _ = export_theory();
