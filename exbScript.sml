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
  matrixTheory matrixLib cf0Theory cf1Theory cf2Theory cf9Theory
  cfaTheory cfbTheory

val _ = new_theory"exb";

Definition b3_def:
  b3 = let d = {"0";"1"} in
    IMAGE (UNCURRY STRCAT o pair$## I (UNCURRY STRCAT))
     (d × d × d)
End

Theorem b3_eq = EVAL ``b3``

Theorem FINITE_b3[simp]:
  FINITE b3
Proof
  rw[b3_eq]
QED

Definition evcn_def:
  evcn c x =
    if c = "c" then x else
    if c = "n" then if x = #"0" then #"1" else #"0" else
    HD c
End

Definition three_def:
  three = mk_cf <| world := b3;
    agent := IMAGE encode_pair ({"0";"1"} × {"0";"1";"c";"n"});
    env := {"0";"1";"c";"n"};
    eval := λa e.
      let d0 = HD (FST (decode_pair a)) in
      let d1 = evcn e d0 in
      let d2 = evcn  (SND (decode_pair a)) d1 in
        [d0;d1;d2] |>
End

Theorem three_in_chu_objects[simp]:
  three ∈ chu_objects b3
Proof
  rw[three_def, in_chu_objects]
  \\ rw[finite_cf_def]
  \\ rw[image_def, PULL_EXISTS, EXISTS_PROD, SUBSET_DEF]
  \\ EVAL_TAC
QED

Theorem three_world[simp]:
  three.world = b3
Proof
  rw[three_def]
QED

Theorem cf_matrix_three:
  cf_matrix three =
    [["000";"010";"000";"010"];
     ["001";"011";"001";"011"];
     ["000";"011";"000";"011"];
     ["001";"010";"001";"010"];
     ["100";"110";"110";"100"];
     ["101";"111";"111";"101"];
     ["100";"111";"111";"100"];
     ["101";"110";"110";"101"]]
Proof
  rw[cf_matrix_def]
  \\ simp[EVAL``three.agent``, EVAL``three.env``]
  \\ qsort_set_to_list_tac
  \\ EVAL_TAC
QED

Definition b3_where_def:
  b3_where i c = { w | w ∈ b3 ∧ EL i w = c }
End

Definition b3_part_def:
  b3_part i = {b3_where i #"0"; b3_where i #"1"}
End

Theorem lt3:
  (i < 3) ⇔ i = 0 ∨ i = 1 ∨ i = 2
Proof
  rw[]
QED

Theorem b3_part_partitions:
  (i < 3) ⇒ partitions (b3_part i) b3
Proof
  reverse(rw[partitions_thm, b3_part_def, GSYM MEMBER_NOT_EMPTY, SUBSET_DEF])
  >- (
    simp[EXISTS_UNIQUE_ALT]
    \\ qexists_tac`b3_where i (EL i y)`
    \\ fs[lt3, b3_eq]
    \\ rw[EQ_IMP_THM]
    \\ rpt (pop_assum mp_tac) \\ EVAL_TAC )
  \\ pop_assum mp_tac \\ rw[b3_where_def]
  \\ fs[lt3, b3_eq]
  \\ dsimp[]
QED

Theorem b3_part_1_not_in_obs_part_three:
  b3_part 1 ∉ obs_part three
Proof
  rw[obs_part_def, b3_part_partitions]
  \\ dsimp[obs_def, b3_part_def]
  \\ rpt disj2_tac
  \\ qexists_tac`encode_pair("0","0")`
  \\ qexists_tac`encode_pair("1","1")`
  \\ conj_tac >- EVAL_TAC
  \\ conj_tac >- EVAL_TAC
  \\ rw[ifs_def]
  \\ Cases_on`a ∈ three.agent` \\ simp[]
  \\ pop_assum mp_tac
  \\ simp[Once three_def, EXISTS_PROD, PULL_EXISTS]
  \\ qx_genl_tac[`a0`,`a1`]
  \\ disch_then assume_tac
  \\ qexists_tac`if a0 = "0" then "0" else "1"`
  \\ pop_assum strip_assume_tac
  \\ rw[] \\ EVAL_TAC
QED

val _ = export_theory();
