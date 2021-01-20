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

structure matrixLib = struct
  local
    open HolKernel boolLib bossLib dep_rewrite
       ASCIInumbersLib listTheory rich_listTheory sortingTheory matrixTheory

    val SET_TO_LIST_tm = ``SET_TO_LIST``

    fun qsort_set_to_list_conv1 tm =
      if listSyntax.is_cons tm andalso
         same_const SET_TO_LIST_tm (rator (#2(listSyntax.dest_cons tm)))
      then
        ONCE_REWRITE_CONV [CONS_APPEND] tm
      else if listSyntax.is_append tm andalso
              listSyntax.is_append (#2 (listSyntax.dest_append tm)) then
        (ONCE_REWRITE_CONV [APPEND_ASSOC] THENC
         LAND_CONV (SIMP_CONV (srw_ss()) [])) tm
      else raise UNCHANGED

    fun qsort_set_to_list_conv2 tm =
      if boolSyntax.is_cond tm then SIMP_CONV(srw_ss())[] tm
      else raise UNCHANGED

  in
    val () = computeLib.add_funs [relationTheory.RC_DEF]
    val qsort_set_to_list_tac =
      simp[QSORT_char_lt_SET_TO_LIST_init]
      \\ rpt (CHANGED_TAC (
        CONV_TAC(DEPTH_CONV qsort_set_to_list_conv1)
        \\ DEP_REWRITE_TAC[QSORT_char_lt_SET_TO_LIST]
        \\ CONV_TAC(DEPTH_CONV qsort_set_to_list_conv2)))
      \\ simp[]
  end
end
