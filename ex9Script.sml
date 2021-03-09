(*
Copyright 2021 DeepMind Technologies Limited.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*)

open HolKernel boolLib bossLib Parse dep_rewrite
  pairTheory pred_setTheory categoryTheory
  cf0Theory ex0Theory cf1Theory cf2Theory cf9Theory

val _ = new_theory"ex9";

Theorem runs3_cf_assume_no_meteor:
  cf_assume_diff {"m"} runs_cf3
  = runs_cf2 with world := runs_cf3.world
Proof
  rw[cf_assume_diff_def]
  \\ rw[runs_cf2_def, runs_cf3_def, cf_component_equality]
  \\ rw[mk_cf_def]
  \\ rw[FUN_EQ_THM]
  \\ rw[]
QED

Theorem runs3_assume_no_meteor:
  assume_diff {"m"} runs_cf3
  = runs_cf2 with world := runs_cf3.world
Proof
  rw[assume_diff_def, GSYM runs3_cf_assume_no_meteor]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ dsimp[runs_cf3_def, SET_EQ_SUBSET, SUBSET_DEF]
  \\ dsimp[EVAL``runs_cf2.env``]
  \\ dsimp[EVAL``runs_cf2.agent``]
  \\ EVAL_TAC
QED

Theorem commit_diff_not_iso_commit:
  ∃w c s.
    c ∈ chu_objects w ∧ s ⊆ w ∧
    ¬ (commit_diff s c ≅ commit (w DIFF s) c -: chu w)
Proof
  qabbrev_tac`w = {"0";"1"}`
  \\ qexists_tac`w`
  \\ qexists_tac`cf1 w w`
  \\ qexists_tac`{"0"}`
  \\ conj_tac >- simp[Abbr`w`]
  \\ conj_tac >- simp[Abbr`w`]
  \\ simp[iso_objs_thm]
  \\ CCONTR_TAC \\ fs[]
  \\ fs[chu_iso_bij]
  \\ gs[maps_to_in_chu]
  \\ ntac 2 (pop_assum mp_tac)
  \\ simp[commit_diff_def, commit_def, cf1_def, mk_cf_def]
  \\ simp[cf_commit_diff_def, cf_commit_def]
  \\ dsimp[Abbr`w`]
  \\ qmatch_goalsub_abbrev_tac`BIJ _ _ s`
  \\ `s = ∅` by simp[EXTENSION, Abbr`s`]
  \\ rw[]
QED

val _ = export_theory();
