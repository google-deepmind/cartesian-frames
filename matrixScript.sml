(*
Copyright 2020 Google LLC

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

open HolKernel boolLib bossLib boolSimps Parse dep_rewrite
  sortingTheory pred_setTheory listTheory relationTheory stringTheory cf0Theory

val _ = new_theory"matrix";

Definition cf_matrix_def:
  cf_matrix c =
   MAP (λa. MAP (c.eval a) (QSORT $<= (SET_TO_LIST c.env)))
       (QSORT $<= (SET_TO_LIST c.agent))
End

Theorem QSORT_string_le_SET_TO_LIST:
∀x.
  (FINITE ls ⇒
   QSORT string_le (x ++ SET_TO_LIST (s INSERT ls)) =
     QSORT string_le (x ++ if s ∈ ls then SET_TO_LIST ls else s::(SET_TO_LIST ls)))
Proof
  gen_tac \\ simp[]
  \\ strip_tac
  \\ DEP_REWRITE_TAC[SORTS_PERM_EQ]
  \\ conj_tac
  >- (
    conj_asm1_tac >- ( rw[transitive_def] \\ metis_tac[string_le_def, string_lt_trans] )
    \\ conj_tac >- ( rw[antisymmetric_def] \\ metis_tac[string_le_def, string_lt_antisym] )
    \\ match_mp_tac QSORT_SORTS
    \\ rw[total_def] \\ metis_tac[string_lt_cases, string_le_def] )
  \\ simp[PERM_APPEND_IFF]
  \\ simp[PERM_SET_TO_LIST_INSERT]
QED

Theorem QSORT_string_le_SET_TO_LIST_init =
  QSORT_string_le_SET_TO_LIST |> Q.SPEC`[]` |> SIMP_RULE(srw_ss())[]

val _ = export_theory();
