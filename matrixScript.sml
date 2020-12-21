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
   MAP (λa. MAP (c.eval a) (QSORT (RC(SHORTLEX char_lt)) (SET_TO_LIST c.env)))
       (QSORT (RC(SHORTLEX char_lt)) (SET_TO_LIST c.agent))
End

Theorem RC_SHORTLEX_char_lt_transitive[simp]:
  transitive (RC (SHORTLEX char_lt))
Proof
  irule transitive_RC
  \\ irule SHORTLEX_transitive
  \\ simp[transitive_def, char_lt_def]
QED

Theorem RC_SHORTLEX_char_lt_total[simp]:
  total (RC (SHORTLEX char_lt))
Proof
  irule SHORTLEX_total
  \\ simp[total_def, RC_DEF, char_lt_def]
  \\ Cases \\ Cases \\ simp[]
QED

Theorem RC_SHORTLEX_char_lt_antisymmetric[simp]:
  antisymmetric (RC (SHORTLEX char_lt))
Proof
  simp[antisymmetric_def]
  \\ Induct \\ simp[]
  \\ gen_tac \\ Cases \\ simp[]
  \\ rw[] \\ fs[] \\ rfs[char_lt_def]
QED

Theorem QSORT_char_lt_SET_TO_LIST:
∀x.
  (FINITE ls ⇒
   QSORT (RC(SHORTLEX char_lt)) (x ++ SET_TO_LIST (s INSERT ls)) =
     QSORT (RC(SHORTLEX char_lt)) (x ++ if s ∈ ls then SET_TO_LIST ls else s::(SET_TO_LIST ls)))
Proof
  gen_tac \\ simp[]
  \\ strip_tac
  \\ DEP_REWRITE_TAC[SORTS_PERM_EQ]
  \\ conj_tac
  >- ( simp[] \\ match_mp_tac QSORT_SORTS \\ simp[])
  \\ simp[PERM_APPEND_IFF]
  \\ simp[PERM_SET_TO_LIST_INSERT]
QED

Theorem QSORT_char_lt_SET_TO_LIST_init =
  QSORT_char_lt_SET_TO_LIST |> Q.SPEC`[]` |> SIMP_RULE(srw_ss())[]

Definition permute_rows_def:
  permute_rows f m = GENLIST (λn. EL (f n) m) (LENGTH m)
End

Definition permute_cols_def:
  permute_cols f m = MAP (λr. GENLIST (λn. EL (f n) r) (LENGTH r)) m
End

Theorem permute_rows_I[simp]:
  permute_rows I m = m
Proof
  rw[permute_rows_def, LIST_EQ_REWRITE]
QED

Theorem permute_cols_I[simp]:
  permute_cols I m = m
Proof
  rw[permute_cols_def, LIST_EQ_REWRITE, EL_MAP]
QED

Theorem permute_rows_cols_comm:
  (∀i. (i < LENGTH m) ⇒ pr i < LENGTH m)
  ⇒
  permute_rows pr (permute_cols pc m) =
  permute_cols pc (permute_rows pr m)
Proof
  rw[permute_rows_def, permute_cols_def]
  \\ simp[LIST_EQ_REWRITE]
  \\ rw[EL_MAP]
QED

Theorem LENGTH_permute_rows[simp]:
  LENGTH (permute_rows pr m) = LENGTH m
Proof
  rw[permute_rows_def]
QED

Theorem LENGTH_permute_cols[simp]:
  LENGTH (permute_cols pc m) = LENGTH m
Proof
  rw[permute_cols_def]
QED

Theorem EL_permute_rows[simp]:
  n < LENGTH m ⇒
  EL n (permute_rows pr m) = EL (pr n) m
Proof
  rw[permute_rows_def]
QED

val _ = export_theory();
