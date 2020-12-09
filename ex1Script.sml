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

open HolKernel boolLib bossLib boolSimps Parse
  pred_setTheory categoryTheory functorTheory
  cf0Theory ex0Theory matrixTheory matrixLib cf1Theory

val _ = new_theory"ex1";

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
