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

Theorem runs3_assume_no_meteor:
  cf_assume_diff {"m"} runs_cf3
  = runs_cf2 with world := runs_cf3.world
Proof
  rw[cf_assume_diff_def]
  \\ rw[runs_cf2_def, runs_cf3_def, cf_component_equality]
  \\ rw[mk_cf_def]
  \\ rw[FUN_EQ_THM]
  \\ rw[]
QED

val _ = export_theory();
