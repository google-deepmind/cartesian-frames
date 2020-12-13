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
  pred_setTheory stringLib
  cf0Theory

val _ = new_theory"ex0";

Definition runs_cf1_def:
  runs_cf1 = mk_cf
    <| agent := { "u"; "n" }; env := { "r"; "s" };
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

Theorem runs1_ensure:
  ensure runs_cf1 = sup_closure runs_cf1.world {{"ur"; "us"}; {"nr"; "ns"}}
Proof
  rw[ensure_def, runs_cf1_def, sup_closure_example]
  \\ rw[SET_EQ_SUBSET, SUBSET_DEF] \\ fs[mk_cf_def]
  \\ fsrw_tac[DNF_ss][] \\ metis_tac[]
QED

Theorem runs1_prevent:
  prevent runs_cf1 = sub_closure runs_cf1.world {{"ur";"us"};{"nr";"ns"}}
Proof
  rw[prevent_def, runs_cf1_def, sub_closure_example]
  \\ rw[SUBSET_DEF]
  \\ rw[Once EXTENSION]
  \\ EQ_TAC \\ rw[] \\ fsrw_tac[DNF_ss][mk_cf_def]
  \\ Cases_on`x = {}` \\ fs[]
  \\ Cases_on`x` \\ fsrw_tac[DNF_ss][] \\ rw[INSERT_EQ_SING]
  \\ Cases_on`t` \\ fsrw_tac[DNF_ss][] \\ rw[INSERT_EQ_SING]
  \\ fs[EXTENSION] \\ metis_tac[]
QED

Theorem runs1_ctrl:
  ctrl runs_cf1 = {{"ur";"us"};{"nr";"ns"}}
Proof
  rw[ctrl_def, runs1_prevent, runs1_ensure, sub_closure_example, sup_closure_example]
  \\ rw[runs_cf1_def]
  \\ rw[EXTENSION] \\ metis_tac[]
QED

Definition runs_cf2_def:
  runs_cf2 = mk_cf
    <| agent := {"u";"n";"run";"sun"};
       env := {"r";"s"};
       world := runs_cf1.world;
       eval := λa e. (if LENGTH a < 2 then EL 0 a else
                      if EL 0 e = EL 0 a then EL 1 a else EL 2 a)::e |>
End

Theorem runs2_ctrl:
  ctrl runs_cf2 = {{"ur";"us"};{"nr";"ns"};{"ur";"ns"};{"nr";"us"}}
Proof
  rw[ctrl_def, ensure_def, prevent_def, runs_cf2_def, runs_cf1_def, SUBSET_DEF]
  \\ rw[Once EXTENSION, mk_cf_def]
  \\ EQ_TAC \\ rw[] \\ fs[]
  \\ spose_not_then strip_assume_tac
  \\ fsrw_tac[DNF_ss][]
  \\ fs[Once EXTENSION]
  \\ metis_tac[]
QED

Definition runs_cf3_def:
  runs_cf3 =
    runs_cf2 with <| env := "m" INSERT runs_cf2.env;
                     world := "m" INSERT runs_cf2.world;
                     eval := λa e. if a ∈ runs_cf2.agent ∧ e = "m" then "m" else runs_cf2.eval a e |>
End

Theorem runs3_ensure:
  ensure runs_cf3 =
    sup_closure runs_cf3.world {{"ur";"us";"m"};{"nr";"ns";"m"};{"ur";"ns";"m"};{"nr";"us";"m"}}
Proof
  rw[ensure_def, runs_cf3_def, runs_cf2_def, runs_cf1_def, mk_cf_def]
  \\ rw[sup_closure_def]
  \\ rw[Once EXTENSION]
  \\ qmatch_goalsub_abbrev_tac`x ⊆ w` \\ Cases_on`x ⊆ w` \\ fs[]
  \\ EQ_TAC \\ rw[] \\ fsrw_tac[DNF_ss][]
QED

Theorem runs3_prevent:
  prevent runs_cf3 =
    sub_closure runs_cf3.world {{"ur";"us"};{"nr";"ns"};{"ur";"ns"};{"nr";"us"}}
Proof
  rw[prevent_def, runs_cf3_def, runs_cf2_def, runs_cf1_def, mk_cf_def]
  \\ rw[sub_closure_def]
  \\ rw[Once EXTENSION]
  \\ qmatch_goalsub_abbrev_tac`x ⊆ w` \\ Cases_on`x ⊆ w` \\ fs[]
  \\ EQ_TAC >- (
    rw[] \\ fsrw_tac[DNF_ss][]
    \\ fsrw_tac[DNF_ss][SUBSET_DEF]
    \\ spose_not_then strip_assume_tac \\ fsrw_tac[DNF_ss][Once EXTENSION, Abbr`w`]
    \\ metis_tac[] )
  \\ strip_tac \\ rpt BasicProvers.var_eq_tac
  THENL (map (exists_tac o fromMLstring) ["n", "u", "sun", "run"])
  \\ rw[] \\ CCONTR_TAC \\ fs[SUBSET_DEF] \\ res_tac \\ fs[]
QED

fun tails [] = []
  | tails (x::y) = (x,y) :: tails y

val envs = ["m","us","ur","ns","nr"]
val ineqs =
  map (fn (x, r) =>
         map (fn y => EVAL(mk_eq(fromMLstring x, fromMLstring y))) r)
      (tails envs) |> List.concat

Theorem runs3_ctrl:
  ctrl runs_cf3 = ∅
Proof
  rw[ctrl_def, runs3_ensure, runs3_prevent]
  \\ rw[sup_closure_def, sub_closure_def, runs_cf3_def, runs_cf2_def, runs_cf1_def]
  \\ rw[GSYM DISJOINT_DEF]
  \\ rw[IN_DISJOINT]
  \\ qmatch_goalsub_abbrev_tac`x ⊆ w`
  \\ Cases_on`x ⊆ w` \\ fs[]
  \\ CCONTR_TAC \\ fs[] \\ rw[] \\ fs[Abbr`w`] \\ fs[SUBSET_DEF]
  \\ metis_tac ineqs
QED

Theorem runs1_obs:
  obs runs_cf1 = union_closure {runs_cf1.world}
Proof
  rw[union_closure_sing, obs_def, EXTENSION, SUBSET_DEF, runs_cf1_def, ifs_def, mk_cf_def]
  \\ rw[Once EQ_IMP_THM]
  \\ fsrw_tac[DNF_ss][]
  \\ metis_tac[]
QED

Theorem wf_runs2[simp]:
  wf runs_cf2
Proof
  rw[runs_cf2_def, image_def, SUBSET_DEF, runs_cf1_def]
  \\ rw[finite_cf_def]
QED

Theorem wf_runs3[simp]:
  wf runs_cf3
Proof
  rw[wf_def, runs_cf3_def, runs_cf2_def, runs_cf1_def, mk_cf_def]
  \\ rw[finite_cf_def]
QED

Theorem runs_cf2_world[simp]:
  runs_cf2.world = runs_cf1.world
Proof
  rw[runs_cf2_def]
QED

(* TODO: both proofs below could probably be streamlined *)

Theorem runs2_obs:
  obs runs_cf2 = union_closure {{"ur";"nr"}; {"us";"ns"}}
Proof
  qmatch_goalsub_abbrev_tac`union_closure s`
  \\ `union_closure s = {{}; runs_cf1.world} ∪ s`
  by (
    rw[Abbr`s`, union_closure_def, runs_cf1_def]
    \\ rw[Once EXTENSION]
    \\ Cases_on`x = {}` \\ fsrw_tac[DNF_ss][]
    \\ Cases_on`x = {"us";"ns"}` \\ fsrw_tac[DNF_ss][]
    >- (qexists_tac`{{"us";"ns"}}` \\ simp[])
    \\ Cases_on`x = {"ur";"nr"}` \\ fsrw_tac[DNF_ss][]
    >- (qexists_tac`{{"ur";"nr"}}` \\ simp[])
    \\ Cases_on`x = {"ur";"us";"nr";"ns"}` \\ fsrw_tac[DNF_ss][]
    >- (qexists_tac`{{"ur";"nr"};{"us";"ns"}}` \\ simp[] \\ simp[EXTENSION] \\ metis_tac[])
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ Cases_on`s` \\ fs[] \\ rw[] \\ fs[]
    \\ Cases_on`t` \\ fs[] \\ rw[] \\ fs[] \\ rw[] \\ fs[] \\ rw[]
    \\ fs[EXTENSION] \\ metis_tac[] )
  \\ pop_assum SUBST1_TAC
  \\ once_rewrite_tac[SET_EQ_SUBSET]
  \\ reverse conj_asm2_tac >- (
    simp[SUBSET_DEF, GSYM CONJ_ASSOC]
    \\ conj_asm1_tac >- simp[obs_empty]
    \\ conj_tac >- (
      first_assum(mp_then Any mp_tac obs_compl)
      \\ simp[runs_cf2_def] )
    \\ pop_assum kall_tac
    \\ simp[Abbr`s`]
    \\ rw[obs_def] \\ TRY (rw[runs_cf2_def, runs_cf1_def, SUBSET_DEF] \\ NO_TAC)
    \\ rw[ifs_def]
    \\ fs[runs_cf2_def, runs_cf1_def, mk_cf_def] \\ rw[]
    \\ TRY(qexists_tac`"u"` \\ rw[] \\ fs[] \\ NO_TAC)
    \\ TRY(qexists_tac`"n"` \\ rw[] \\ fs[] \\ NO_TAC)
    \\ TRY(qexists_tac`"run"` \\ rw[] \\ fs[] \\ NO_TAC)
    \\ TRY(qexists_tac`"sun"` \\ rw[] \\ fs[] \\ NO_TAC))
  \\ rw[SUBSET_DEF]
  \\ CCONTR_TAC \\ fs[]
  \\ qpat_x_assum`x ∈ _`mp_tac
  \\ rw[obs_def, runs_cf2_def]
  \\ Cases_on`x ⊆ runs_cf1.world` \\ fs[]
  \\ fs[Abbr`s`]
  \\ simp[mk_cf_def]
  \\ Cases_on`x = {"ur"}`
  >- (
    qexists_tac`"n"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"nr"}`
  >- (
    qexists_tac`"u"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us"}`
  >- (
    qexists_tac`"n"` \\ qexists_tac`"u"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ns"}`
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ns";"nr"}`
  >- (
    qexists_tac`"run"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us";"ur"}`
  >- (
    qexists_tac`"run"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ur";"ns"}`
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us";"nr"}`
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us";"ur";"ns"}`
  >- (
    qexists_tac`"n"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us";"ur";"nr"}`
  >- (
    qexists_tac`"n"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ns";"ur";"nr"}`
  >- (
    qexists_tac`"u"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ns";"us";"nr"}`
  >- (
    qexists_tac`"u"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ `F` suffices_by rw[]
  \\ qpat_x_assum`x ⊆ _`mp_tac
  \\ fs[runs_cf1_def]
  \\ simp[GSYM IN_POW]
  \\ simp[POW_EQNS]
  \\ fs[INSERT_COMM]
QED

Theorem runs3_obs:
  obs runs_cf3 = union_closure {{"ur";"nr"};{"us";"ns"};{"m"}}
Proof
  qmatch_goalsub_abbrev_tac`union_closure s`
  \\ `union_closure s = s ∪
        {{}; runs_cf3.world; {"ur";"nr";"us";"ns"}; {"ur";"nr";"m"}; {"us";"ns";"m"}}`
  by (
    rw[Abbr`s`, runs_cf3_def, runs_cf2_def, runs_cf1_def]
    \\ rw[Once EXTENSION]
    \\ rw[union_closure_def]
    \\ Cases_on`x = {}` \\ fsrw_tac[DNF_ss][]
    \\ Cases_on`x = {"m"}` \\ fsrw_tac[DNF_ss][]
    >- (qexists_tac`{{"m"}}` \\ simp[])
    \\ qmatch_goalsub_abbrev_tac`x = s ∨ _`
    \\ Cases_on`x = s` \\ fsrw_tac[DNF_ss][]
    >- (qexists_tac`{s}` \\ simp[])
    \\ qunabbrev_tac`s`
    \\ qmatch_goalsub_abbrev_tac`x = s ∨ _`
    \\ Cases_on`x = s` \\ fsrw_tac[DNF_ss][]
    >- (qexists_tac`{s}` \\ simp[])
    \\ qunabbrev_tac`s`
    \\ qmatch_goalsub_abbrev_tac`x = s ∨ _`
    \\ Cases_on`x = s` \\ fsrw_tac[DNF_ss][]
    >- (
      qmatch_goalsub_abbrev_tac`_ ⊆ t`
      \\ qexists_tac`t`
      \\ simp[Abbr`s`,Abbr`t`]
      \\ simp[EXTENSION] \\ PROVE_TAC[])
    \\ qunabbrev_tac`s`
    \\ qmatch_goalsub_abbrev_tac`x = s ∨ _`
    \\ Cases_on`x = s` \\ fsrw_tac[DNF_ss][]
    >- (
      qmatch_goalsub_abbrev_tac`_ ⊆ {s1;s2;s3}`
      \\ qexists_tac`{s1;s2}`
      \\ simp[Abbr`s`,Abbr`s1`,Abbr`s2`]
      \\ simp[EXTENSION] \\ PROVE_TAC[])
    \\ qunabbrev_tac`s`
    \\ qmatch_goalsub_abbrev_tac`x = s ∨ _`
    \\ Cases_on`x = s` \\ fsrw_tac[DNF_ss][]
    >- (
      qmatch_goalsub_abbrev_tac`_ ⊆ {s1;s2;s3}`
      \\ qexists_tac`{s1;s3}`
      \\ simp[Abbr`s`,Abbr`s1`,Abbr`s3`]
      \\ simp[EXTENSION] \\ PROVE_TAC[])
    \\ qunabbrev_tac`s`
    \\ qmatch_goalsub_abbrev_tac`x = s`
    \\ Cases_on`x = s` \\ fsrw_tac[DNF_ss][]
    >- (
      qmatch_goalsub_abbrev_tac`_ ⊆ {s1;s2;s3}`
      \\ qexists_tac`{s2;s3}`
      \\ simp[Abbr`s`,Abbr`s2`,Abbr`s3`]
      \\ simp[EXTENSION] \\ PROVE_TAC[])
    \\ qunabbrev_tac`s`
    \\ rw[GSYM IN_POW]
    \\ simp[POW_EQNS]
    \\ CCONTR_TAC \\ fs[] \\ rw[] \\ fs[] \\ fs[EXTENSION]
    \\ metis_tac[])
  \\ pop_assum SUBST1_TAC
  \\ qunabbrev_tac `s`
  \\ simp[SimpRHS, runs_cf3_def, runs_cf2_def, runs_cf1_def]
  \\ once_rewrite_tac[SET_EQ_SUBSET]
  \\ reverse conj_asm2_tac >- (
    simp[SUBSET_DEF, GSYM CONJ_ASSOC]
    \\ `∅ ∈ obs runs_cf3` by simp[obs_empty]
    \\ first_assum(mp_then Any mp_tac obs_compl)
    \\ simp[]
    \\ simp[Once runs_cf3_def, runs_cf2_def, runs_cf1_def]
    \\ strip_tac
    \\ `{"m"} ∈ obs runs_cf3`
    by (
      simp[obs_def]
      \\ conj_tac >- EVAL_TAC
      \\ rpt gen_tac \\ strip_tac
      \\ qexists_tac`a1` \\ simp[]
      \\ simp[ifs_def]
      \\ ntac 2 (pop_assum mp_tac)
      \\ EVAL_TAC
      \\ rw[])
    \\ first_assum (mp_then Any mp_tac obs_compl)
    \\ simp[]
    \\ simp[Once runs_cf3_def, runs_cf2_def, runs_cf1_def, INSERT_COMM]
    \\ strip_tac
    \\ `{"ur";"nr"} ∈ obs runs_cf3`
    by (
      simp[obs_def]
      \\ conj_tac >- EVAL_TAC
      \\ rpt gen_tac \\ strip_tac
      \\ simp[ifs_def, runs_cf3_def, runs_cf2_def, mk_cf_def]
      \\ fs[runs_cf3_def, runs_cf2_def, runs_cf1_def]
      \\ TRY(qexists_tac`"u"` \\ rw[] \\ fs[] \\ NO_TAC)
      \\ TRY(qexists_tac`"n"` \\ rw[] \\ fs[] \\ NO_TAC)
      \\ TRY(qexists_tac`"run"` \\ rw[] \\ fs[] \\ NO_TAC)
      \\ TRY(qexists_tac`"sun"` \\ rw[] \\ fs[] \\ NO_TAC))
    \\ first_assum (mp_then Any mp_tac obs_compl)
    \\ simp[]
    \\ simp[Once runs_cf3_def, runs_cf2_def, runs_cf1_def, INSERT_COMM]
    \\ strip_tac
    \\ `{"us";"ns"} ∈ obs runs_cf3`
    by (
      simp[obs_def]
      \\ conj_tac >- EVAL_TAC
      \\ rpt gen_tac \\ strip_tac
      \\ simp[ifs_def, runs_cf3_def, runs_cf2_def, mk_cf_def]
      \\ fs[runs_cf3_def, runs_cf2_def, runs_cf1_def]
      \\ TRY(qexists_tac`"u"` \\ rw[] \\ fs[] \\ NO_TAC)
      \\ TRY(qexists_tac`"n"` \\ rw[] \\ fs[] \\ NO_TAC)
      \\ TRY(qexists_tac`"run"` \\ rw[] \\ fs[] \\ NO_TAC)
      \\ TRY(qexists_tac`"sun"` \\ rw[] \\ fs[] \\ NO_TAC))
    \\ first_assum (mp_then Any mp_tac obs_compl)
    \\ simp[]
    \\ simp[Once runs_cf3_def, runs_cf2_def, runs_cf1_def, INSERT_COMM])
  \\ rw[SUBSET_DEF]
  \\ CCONTR_TAC \\ fs[]
  \\ qpat_x_assum`x ∈ _`mp_tac
  \\ rw[obs_def, runs_cf3_def, runs_cf2_def, runs_cf1_def, mk_cf_def]
  \\ simp[Once (GSYM IMP_DISJ_THM)]
  \\ simp[GSYM IN_POW]
  \\ simp[POW_EQNS]
  \\ fs[INSERT_COMM]
  \\ Cases_on`x = {"ns"}` \\ fs[]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"nr"}` \\ fs[]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us"}` \\ fs[]
  >- (
    qexists_tac`"n"` \\ qexists_tac`"u"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ur"}` \\ fs[]
  >- (
    qexists_tac`"n"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ns";"nr"}` \\ fs[]
  >- (
    qexists_tac`"run"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us";"ur"}` \\ fs[]
  >- (
    qexists_tac`"run"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ur";"ns"}` \\ fs[]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us";"nr"}` \\ fs[]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us";"ur";"ns"}` \\ fs[INSERT_COMM]
  >- (
    qexists_tac`"n"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us";"ur";"nr"}` \\ fs[INSERT_COMM]
  >- (
    qexists_tac`"n"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ns";"ur";"nr"}` \\ fs[INSERT_COMM]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ns";"us";"nr"}` \\ fs[INSERT_COMM]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ fs[INSERT_COMM, GSYM DISJ_ASSOC]
  \\ Cases_on`x = {"m"; "ns"}` \\ fs[]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m"; "nr"}` \\ fs[]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m"; "us"}` \\ fs[]
  >- (
    qexists_tac`"n"` \\ qexists_tac`"u"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m"; "ur"}` \\ fs[]
  >- (
    qexists_tac`"n"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m"; "ns";"nr"}` \\ fs[]
  >- (
    qexists_tac`"run"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m";"us";"ur"}` \\ fs[]
  >- (
    qexists_tac`"run"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m";"ur";"ns"}` \\ fs[]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m";"us";"nr"}` \\ fs[]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m";"us";"ur";"ns"}` \\ fs[INSERT_COMM]
  >- (
    qexists_tac`"n"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m";"us";"ur";"nr"}` \\ fs[INSERT_COMM]
  >- (
    qexists_tac`"n"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m";"ns";"ur";"nr"}` \\ fs[INSERT_COMM]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m";"ns";"us";"nr"}` \\ fs[INSERT_COMM]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
QED

Definition runs_cf4_def:
  runs_cf4 = mk_cf
    <| world := runs_cf1.world; agent := {""}; env := runs_cf1.world; eval := λa e. e |>
End

Definition runs_cf5_def:
  runs_cf5 = mk_cf
    <| world := runs_cf1.world; env := {""}; agent := runs_cf1.world; eval := λa e. a |>
End

(* TODO: facts about runs_cf4, runs_cf5 *)

val _ = export_theory();
