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
  relationTheory pred_setTheory listTheory rich_listTheory
  stringTheory sortingTheory ASCIInumbersLib
  categoryTheory functorTheory
  cf0Theory ex0Theory cf1Theory

val _ = new_theory"ex1";

(* TODO: move *)

Theorem SORTS_PERM_EQ:
  transitive R ∧ antisymmetric R ∧ SORTS f R ∧ PERM l1 l2 ⇒
    f R l1 = f R l2
Proof
  strip_tac
  \\ match_mp_tac (MP_CANON SORTED_PERM_EQ)
  \\ qexists_tac`R` \\ simp[]
  \\ fs[SORTS_DEF]
  \\ `PERM (f R l1) l1` by metis_tac[PERM_SYM]
  \\ `PERM l2 (f R l2)` by metis_tac[]
  \\ metis_tac[PERM_TRANS]
QED

Theorem PERM_SET_TO_LIST_INSERT:
  FINITE y ⇒
    PERM
      (SET_TO_LIST (x INSERT y))
      (if x ∈ y then SET_TO_LIST y else x :: SET_TO_LIST y)
Proof
  rw[] >- ( `x INSERT y = y` by (simp[EXTENSION] \\ metis_tac[]) \\ rw[] )
  \\ Cases_on`CHOICE (x INSERT y) = x`
  >- (
    rw[]
    \\ simp[Once SET_TO_LIST_THM]
    \\ `REST (x INSERT y) = y`
    by (
      qspec_then`x INSERT y`mp_tac CHOICE_INSERT_REST
      \\ simp[]
      \\ qspec_then`x INSERT y`mp_tac (CONV_RULE SWAP_FORALL_CONV IN_REST)
      \\ simp[]
      \\ rw[EXTENSION]
      \\ metis_tac[] )
    \\ simp[] )
  \\ simp[Once SET_TO_LIST_THM]
  \\ match_mp_tac PERM_ALL_DISTINCT
  \\ simp[CHOICE_NOT_IN_REST]
  \\ metis_tac[CHOICE_INSERT_REST, NOT_EMPTY_INSERT, IN_INSERT]
QED

(* -- *)

Definition test_world_def:
  test_world = "F" INSERT BIGUNION (IMAGE (λg. {g;g++"+";g++"-"}) {"A";"B";"C";"D"})
End

Theorem test_world_eq = EVAL ``test_world``

Definition test_today_def:
  test_today = mk_cf
    <| world := test_world;
       env := {"t";"d";"o"};
       agent := {"s";"i"};
       eval := λa e. if a = "i" then "C+" else
                     if e = "t" then "A-" else
                     if e = "d" then "B+" else "D-" |>
End

Definition test_yesterday_def:
  test_yesterday = mk_cf
    <| world := test_world;
       env := test_today.env;
       agent := "c" INSERT test_today.agent;
       eval := λa e. if a = "c" then "A+" else test_today.eval a e |>
End

Definition test_demanding_def:
  test_demanding = mk_cf
    <| world := test_world;
       env := test_today.env DELETE "t";
       agent := test_today.agent;
       eval := test_today.eval |>
End

Theorem morphism_today_yesterday:
  is_chu_morphism test_today test_yesterday
    (mk_chu_morphism test_today test_yesterday <| map_env := I; map_agent := I |>).map
Proof
  simp[is_chu_morphism_def]
  \\ simp[mk_chu_morphism_def]
  \\ rw[test_today_def, test_yesterday_def, categoryTheory.restrict_def, mk_cf_def]
QED

Theorem morphism_today_demanding:
  is_chu_morphism test_today test_demanding
    (mk_chu_morphism test_today test_demanding <| map_env := I; map_agent := I |>).map
Proof
  simp[is_chu_morphism_def]
  \\ simp[mk_chu_morphism_def]
  \\ rw[test_today_def, test_demanding_def, categoryTheory.restrict_def, mk_cf_def]
QED

Theorem no_morphisms_yesterday_demanding:
  ¬is_chu_morphism test_yesterday test_demanding m ∧
  ¬is_chu_morphism test_demanding test_yesterday m
Proof
  Cases_on`m`
  \\ qmatch_goalsub_rename_tac`chu_morphism_map f g`
  \\ simp[is_chu_morphism_def]
  \\ conj_tac
  \\ (qmatch_abbrev_tac`a ∨ b` \\ Cases_on`a = T` \\ fs[Abbr`a`, Abbr`b`])
  \\ (qmatch_abbrev_tac`a ∨ b` \\ Cases_on`a = T` \\ fs[Abbr`a`, Abbr`b`])
  \\ (qmatch_abbrev_tac`a ∨ b` \\ Cases_on`a = T` \\ fs[Abbr`a`, Abbr`b`]
      >- metis_tac[] \\ disj2_tac)
  \\ (qmatch_abbrev_tac`a ∨ b` \\ Cases_on`a = T` \\ fs[Abbr`a`, Abbr`b`]
      >- metis_tac[] \\ disj2_tac)
  \\ fs[GSYM IMP_DISJ_THM]
  \\ fs[test_yesterday_def, test_demanding_def, test_today_def, mk_cf_def]
  >- (
    qexists_tac`"c"` \\ simp[]
    \\ qexists_tac`"d"` \\ rw[] )
  \\ qexists_tac`if f "i" = "i" then "s" else "i"`
  \\ qexists_tac`"t"`
  \\ simp[]
  \\ IF_CASES_TAC \\ simp[] \\ rw[] \\ fs[]
  \\ metis_tac[]
QED

Definition handshake_def:
  handshake = mk_cf
    <| world := {""; "*"};
       agent := {""; "*"};
       env := {""; "*"};
       eval := λa e. DROP 1 (a ++ e) |>
End

Definition bothsing_def:
  bothsing = mk_cf
    <| world := {""};
       agent := {""};
       env := {""};
       eval := K (K "") |>
End

Theorem morphism_handshake_bothsing:
  is_chu_morphism handshake bothsing
    (mk_chu_morphism handshake bothsing <| map_agent := K ""; map_env := K "" |>).map
Proof
  simp[is_chu_morphism_def, handshake_def, bothsing_def, mk_chu_morphism_def]
  \\ rw[] \\ EVAL_TAC
QED

Theorem morphism_bothsing_handshake:
  is_chu_morphism bothsing handshake
    (mk_chu_morphism bothsing handshake <| map_agent := K ""; map_env := K "" |>).map
Proof
  simp[is_chu_morphism_def, handshake_def, bothsing_def, mk_chu_morphism_def]
  \\ rw[] \\ EVAL_TAC
QED

Definition sum_exc_def:
  sum_exc = mk_cf
    <| world := IMAGE toString (count 13);
       agent := IMAGE toString (count 2);
       env := IMAGE toString (count 2);
       eval := λa e. toString (toNum (a) * 2 + toNum(e)) |>
End

Definition sum_exd_def:
  sum_exd = mk_cf
    <| world := IMAGE toString (count 13);
       agent := IMAGE toString (count 3);
       env := IMAGE toString (count 3);
       eval := λa e. toString (4 + toNum(a) * 3 + toNum(e)) |>
End

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
  \\ match_mp_tac SORTS_PERM_EQ
  \\ conj_asm1_tac >- ( rw[transitive_def] \\ metis_tac[string_le_def, string_lt_trans] )
  \\ conj_tac >- ( rw[antisymmetric_def] \\ metis_tac[string_le_def, string_lt_antisym] )
  \\ conj_tac
  >- ( match_mp_tac QSORT_SORTS
    \\ rw[total_def] \\ metis_tac[string_lt_cases, string_le_def] )
  \\ simp[PERM_APPEND_IFF]
  \\ simp[PERM_SET_TO_LIST_INSERT]
QED

Theorem QSORT_string_le_SET_TO_LIST_init =
  QSORT_string_le_SET_TO_LIST |> Q.SPEC`[]` |> SIMP_RULE(srw_ss())[]

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

val qsort_set_to_list_tac =
  simp[QSORT_string_le_SET_TO_LIST_init]
  \\ rpt (CHANGED_TAC (
    CONV_TAC(DEPTH_CONV qsort_set_to_list_conv1)
    \\ DEP_REWRITE_TAC[QSORT_string_le_SET_TO_LIST]
    \\ CONV_TAC(DEPTH_CONV qsort_set_to_list_conv2)))
  \\ simp[]

Theorem cf_matrix_sum_exc:
  cf_matrix sum_exc =
    [ ["0"; "1"];
      ["2"; "3"] ]
Proof
  rw[cf_matrix_def, sum_exc_def]
  \\ CONV_TAC(DEPTH_CONV(fn tm =>
        if pred_setSyntax.is_image tm then EVAL tm else
        raise UNCHANGED))
  \\ simp[QSORT_string_le_SET_TO_LIST_init, mk_cf_def]
  \\ EVAL_TAC
QED

Theorem cf_matrix_sum_exd:
  cf_matrix sum_exd =
    [ ["4"; "5"; "6"];
      ["7"; "8"; "9"];
      ["10"; "11"; "12"] ]
Proof
  rw[cf_matrix_def, sum_exd_def]
  \\ CONV_TAC(DEPTH_CONV(fn tm =>
        if pred_setSyntax.is_image tm then EVAL tm else
        raise UNCHANGED))
  \\ simp[mk_cf_def]
  \\ qsort_set_to_list_tac
  \\ EVAL_TAC
QED

Theorem cf_matrix_sum_exc_exd:
  cf_matrix (sum sum_exc sum_exd) =
    [ ["0"; "0"; "0"; "1"; "1"; "1"];
      ["2"; "2"; "2"; "3"; "3"; "3"];
      ["4"; "5"; "6"; "4"; "5"; "6"];
      ["7"; "8"; "9"; "7"; "8"; "9"];
      ["10"; "11"; "12"; "10"; "11"; "12"]]
Proof
  simp[cf_matrix_def]
  \\ simp[sum_def]
  \\ simp[sum_exc_def, sum_exd_def]
  \\ CONV_TAC(DEPTH_CONV(fn tm =>
        if pred_setSyntax.is_image tm then EVAL tm else
        raise UNCHANGED))
  \\ simp[INSERT_UNION, mk_cf_def]
  \\ qsort_set_to_list_tac
  \\ EVAL_TAC
QED

Theorem cf_matrix_prod_exc_exd:
  cf_matrix (prod sum_exc sum_exd) =
    [ ["0"; "1";  "4";  "5";  "6"];
      ["0"; "1";  "7";  "8";  "9"];
      ["0"; "1"; "10"; "11"; "12"];
      ["2"; "3";  "4";  "5";  "6"];
      ["2"; "3";  "7";  "8";  "9"];
      ["2"; "3"; "10"; "11"; "12"] ]
Proof
  simp[cf_matrix_def]
  \\ simp[prod_def]
  \\ simp[sum_exc_def, sum_exd_def]
  \\ CONV_TAC(DEPTH_CONV(fn tm =>
        if pred_setSyntax.is_image tm then EVAL tm else
        raise UNCHANGED))
  \\ simp[INSERT_UNION, mk_cf_def]
  \\ qsort_set_to_list_tac
  \\ EVAL_TAC
QED

Theorem cf_matrix_runs_cf2:
  cf_matrix runs_cf2 =
    [
      (* n *)  ["nr"; "ns"];
      (* run *)["ur"; "ns"];
      (* sun *)["nr"; "us"];
      (* u *)  ["ur"; "us"];
    ]
Proof
  simp[cf_matrix_def, runs_cf2_def]
  \\ qsort_set_to_list_tac
  \\ EVAL_TAC
QED

Definition run_cf_def:
  run_cf = mk_cf
    <| world := runs_cf1.world;
       agent := {"u"; "n"};
       env := {"r"};
       eval := (++) |>
End

Definition sun_cf_def:
  sun_cf = mk_cf
    <| world := runs_cf1.world;
       agent := {"u"; "n"};
       env := {"s"};
       eval := (++) |>
End

Theorem wf_run_sun[simp]:
  wf run_cf ∧ wf sun_cf
Proof
  rw[run_cf_def, sun_cf_def, image_def]
  \\ rw[SUBSET_DEF]
  \\ EVAL_TAC
QED

Theorem run_sun_world[simp]:
  run_cf.world = runs_cf1.world ∧
  sun_cf.world = runs_cf1.world
Proof
  rw[run_cf_def, sun_cf_def]
QED

Theorem run_sun_in_chu_objects[simp]:
  run_cf ∈ chu_objects runs_cf1.world ∧
  sun_cf ∈ chu_objects runs_cf1.world
Proof
  rw[chu_objects_def]
QED

Theorem runs2_in_chu_objects[simp]:
  runs_cf2 ∈ chu_objects runs_cf1.world
Proof
  rw[chu_objects_def]
QED

Theorem runs_cf2_as_product:
  runs_cf2 ≅ run_cf && sun_cf -: chu (runs_cf1.world)
Proof
  simp[iso_objs_thm]
  \\ qexists_tac`mk_chu_morphism (runs_cf2) (run_cf && sun_cf)
                   <| map_agent :=
                        (λa. encode_pair (if a = "u" ∨ a = "run" then "u" else "n",
                                          if a = "n" ∨ a = "run" then "n" else "u"));
                      map_env := TL |>`
  \\ simp[maps_to_in_def]
  \\ simp[pre_chu_def]
  \\ simp[chu_iso_bij]
  \\ reverse conj_asm1_tac \\ simp[]
  >- (
    simp[mk_chu_morphism_def]
    \\ conj_tac
    >- (
      simp[BIJ_IFF_INV]
      \\ conj_tac >- rw[runs_cf2_def, restrict_def, prod_def, run_cf_def, sun_cf_def]
      \\ qexists_tac`λa.
          let a = DROP 2 a in
          if HD a = HD (TL a) then TAKE 1 a else
          if HD a = #"u" then "run" else "sun"`
      \\ rw[runs_cf2_def, run_cf_def, sun_cf_def, prod_def, pairTheory.EXISTS_PROD]
      \\ rpt (pop_assum mp_tac)
      \\ EVAL_TAC )
    >- (
      simp[BIJ_IFF_INV]
      \\ conj_tac >- (EVAL_TAC \\ rw[] \\ rw[])
      \\ qexists_tac`λe. if e = "r" then "lr" else "rs"`
      \\ rw[runs_cf2_def, run_cf_def, sun_cf_def, prod_def, pairTheory.EXISTS_PROD]
      \\ rpt(pop_assum mp_tac)
      \\ EVAL_TAC ))
  \\ simp[mk_chu_morphism_def]
  \\ simp[is_chu_morphism_def]
  \\ rw[runs_cf2_def, run_cf_def, sun_cf_def, restrict_def, prod_def] \\ fs[] \\ rw[]
  \\ rpt (pop_assum mp_tac) \\ EVAL_TAC
QED

val _ = export_theory();
