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

(* these could be used elsewhere *)

Definition encode_repfn_def:
  encode_repfn b q = encode_function (IMAGE encode_set b)
    (restrict (q o decode_set) (IMAGE encode_set b))
End

Theorem encode_repfn_in_repfns:
  FINITE b ∧ EVERY_FINITE b ∧ extensional q b ⇒
  (encode_repfn b q ∈ repfns b ⇔ is_repfn b q)
Proof
  rw[repfns_def, encode_repfn_def]
  \\ reverse EQ_TAC >- metis_tac[]
  \\ strip_tac
  \\ fs[is_repfn_def]
  \\ rpt strip_tac
  \\ `q x = q' x` suffices_by rw[]
  \\ first_x_assum(mp_tac o Q.AP_TERM`decode_function`)
  \\ disch_then(mp_tac o C Q.AP_THM `encode_set x`)
  \\ simp[]
  \\ rw[restrict_def]
  \\ metis_tac[]
QED

(* -- *)

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

Definition ext0_three_def:
  ext0_three = mk_cf <| world := b3;
    agent := IMAGE (UNCURRY STRCAT) ({"0";"1"} × b3);
    env := IMAGE (UNCURRY STRCAT) ({"0";"1"} × {"0";"1"});
    eval := λa e. SNOC (EL (ORD (EL 1 e) - ORD #"0" +
                        2 * (ORD (EL 0 e) - ORD #"0")) a) e
    |>
End

Theorem ext0_three_agent_eq = EVAL``ext0_three.agent``
Theorem ext0_three_env_eq = EVAL``ext0_three.env``

Theorem cf_matrix_ext0_three:
  cf_matrix (ext0_three) =
  [["000";"010";"100";"110"];
   ["000";"010";"100";"111"];
   ["000";"010";"101";"110"];
   ["000";"010";"101";"111"];
   ["000";"011";"100";"110"];
   ["000";"011";"100";"111"];
   ["000";"011";"101";"110"];
   ["000";"011";"101";"111"];
   ["001";"010";"100";"110"];
   ["001";"010";"100";"111"];
   ["001";"010";"101";"110"];
   ["001";"010";"101";"111"];
   ["001";"011";"100";"110"];
   ["001";"011";"100";"111"];
   ["001";"011";"101";"110"];
   ["001";"011";"101";"111"]]
Proof
  rw[cf_matrix_def]
  \\ rw[ext0_three_agent_eq, ext0_three_env_eq]
  \\ qsort_set_to_list_tac
  \\ EVAL_TAC
QED

Theorem ext0_three_in_chu_objects[simp]:
  ext0_three ∈ chu_objects b3
Proof
  rw[ext0_three_def, in_chu_objects, finite_cf_def]
  \\ rw[image_def, SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
  \\ pop_assum mp_tac \\ rw[b3_eq] \\ rw[]
QED

Definition unevcn_def:
  unevcn d0 s =
    let s = if d0 = #"0" then TAKE 2 s else DROP 2 s in
    if s = "00" then "0" else
    if s = "01" then "c" else
    if s = "10" then "n" else
    "1"
End

Theorem evcn_in:
  x ∈ {#"0";#"1"} ∧ c ∈ {"c";"n";"0";"1"} ⇒
  evcn c x ∈ {#"0";#"1"}
Proof
  rw[evcn_def] \\ rw[]
QED

Theorem three_eval:
  three.eval a e =
  if a ∈ three.agent ∧ e ∈ three.env then
      let d0 = HD (FST (decode_pair a)) in
      let d1 = evcn e d0 in
      let d2 = evcn  (SND (decode_pair a)) d1 in
        [d0;d1;d2]
  else ARB
Proof
  rw[three_def, mk_cf_def, restrict_def]
QED

Theorem ext0_three_eval:
  ext0_three.eval a e =
  if a ∈ ext0_three.agent ∧ e ∈ ext0_three.env then
    SNOC (EL (ORD (EL 1 e) - ORD #"0" + TWICE (ORD (EL 0 e) - ORD #"0")) a) e
  else ARB
Proof
  rw[ext0_three_def, mk_cf_def, restrict_def]
QED

Theorem b3_where_inj:
  (i < 3) ∧ d ∈ {#"0";#"1"} ∧ d' ∈ {#"0";#"1"} ⇒
  (b3_where i d = b3_where i d' ⇔ (d = d'))
Proof
  strip_tac
  \\ rw[b3_where_def, Once EXTENSION]
  \\ EQ_TAC \\ simp[]
  \\ fs[lt3, b3_eq]
  \\ metis_tac[
       listTheory.EL,
       EVAL``EL 0 [a;b;c]``,
       EVAL``EL 1 [a;b;c]``,
       EVAL``EL 2 [a;b;c]``,
       EVAL``#"0"=#"1"``]
QED

Theorem three_eval_b3_part_0:
  p ∈ three.agent ∧ e ∈ three.env ⇒
  (@w. w ∈ b3_part 0 ∧ three.eval p e ∈ w) =
  b3_where 0 (HD(FST (decode_pair p)))
Proof
  strip_tac
  \\ SELECT_ELIM_TAC
  \\ conj_tac >- metis_tac[b3_part_partitions, EVAL``0 < 3``, partitions_thm,
                           three_in_chu_objects, in_chu_objects, wf_def]
  \\ simp[three_eval]
  \\ rw[b3_part_def]
  \\ DEP_REWRITE_TAC[b3_where_inj]
  \\ simp[]
  \\ fs[b3_where_def]
QED

Theorem EL_4:
  f0 ∈ {#"0";#"1"} ∧
  f1 ∈ {#"0";#"1"}
  ⇒
  EL (ORD f1 - 48 + TWICE (ORD f0 - 48))
    ((f #"0" #"0")::(f #"0" #"1")::(f #"1" #"0")::(f #"1" #"1")::"")
  = f f0 f1
Proof
  rw[] \\ rw[]
QED

Theorem evcn_idem:
  c ∈ three.env ∧ x ∈ {#"0";#"1"} ⇒
  evcn (evcn c x :: []) x =
  evcn c x
Proof
  rw[evcn_def] \\ gs[]
  \\ gs[three_def]
QED

Theorem homotopy_equiv_ext0_three:
  external (b3_part 0) three ≃ ext0_three -: b3
Proof
  rw[homotopy_equiv_def]
  \\ qexists_tac`mk_chu_morphism (external (b3_part 0) three) ext0_three
      <| map_agent :=
          λq.
          (*
          q - pick representative (1st, (2nd -> 3rd)) given an equivalence
              class of all such agents that fix the 1st digit
          want: choice of 3rd for all (1st, 2nd)
          strategy, for each (1st, 2nd),
            let (1st', func) = q (equiv_class_for (1st, K 0))
            in func 2nd
          *)
          MAP (λe.
            let fp = fn_part three.agent three.env three.eval (b3_part 0) in
            let p = encode_pair ([EL 0 e], "0") in
            let a = decode_function q (encode_set (fp p)) in
            evcn (SND (decode_pair a)) (EL 1 e))
            ["00";"01";"10";"11"];
         map_env := λe.
           encode_pair (encode_set
             (fn_part three.agent three.env three.eval (b3_part 0)
               (encode_pair ([EL 0 e], "0"))),
              [EL 1 e]) |>`
  \\ qmatch_goalsub_abbrev_tac`homotopic _ (_ o h -: _) _`
  \\ qexists_tac`mk_chu_morphism ext0_three (external (b3_part 0) three) <|
       map_agent := λa.
         let fp = fn_partition three.agent three.env three.eval (b3_part 0) in
         encode_repfn fp
         (restrict (λs.
             let d0 = FST (decode_pair (CHOICE s)) in
             encode_pair (d0, unevcn (HD d0) a)) fp);
       map_env := λp.
         let d0 = HD(FST(decode_pair(CHOICE(decode_set(FST(decode_pair p)))))) in
         let d1 = evcn (SND(decode_pair p)) d0 in
         [d0; d1] |>`
  \\ qmatch_goalsub_abbrev_tac`homotopic _ (g o h -: _) _`
  \\ `partitions (b3_part 0) b3` by simp[b3_part_partitions]
  \\ qmatch_asmsub_abbrev_tac`LET _ fp`
  \\ `partitions fp three.agent`
  by(
    qunabbrev_tac`fp`
    \\ irule partitions_fn_partition
    \\ qexists_tac`b3`
    \\ simp[]
    \\ metis_tac[three_in_chu_objects, in_chu_objects, wf_def])
  \\ drule partitions_FINITE
  \\ impl_keep_tac >- simp[three_def]
  \\ strip_tac
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu, Abbr`h`, b3_part_partitions]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ conj_asm1_tac
    >- (
      simp[external_def, cf_external_def]
      \\ gen_tac \\ strip_tac
      \\ conj_tac
      >- (
        qmatch_goalsub_abbrev_tac`encode_set s`
        \\ qexists_tac`s` \\ simp[]
        \\ simp[Abbr`s`, Abbr`fp`, fn_partition_def]
        \\ qmatch_goalsub_abbrev_tac`_ x = _ ∧ _`
        \\ qexists_tac`x` \\ simp[]
        \\ simp[Abbr`x`]
        \\ simp[three_def]
        \\ pop_assum mp_tac
        \\ rw[ext0_three_env_eq] \\ simp[])
      \\ pop_assum mp_tac
      \\ rw[ext0_three_env_eq] \\ simp[three_def])
    \\ conj_asm1_tac
    >- (
      simp[external_def, cf_external_def]
      \\ simp[repfns_def]
      \\ gen_tac \\ strip_tac
      \\ qmatch_goalsub_abbrev_tac`encode_set (f _)`
      \\ simp[ext0_three_def, EXISTS_PROD, b3_def]
      \\ qmatch_goalsub_abbrev_tac`a0::b::c::d`
      \\ qexists_tac`[a0]` \\ simp[PULL_EXISTS]
      \\ qexists_tac`[b]` \\ simp[]
      \\ qexists_tac`[c]` \\ simp[]
      \\ simp[Abbr`d`]
      \\ qmatch_goalsub_abbrev_tac`evcn d _`
      \\ simp[Abbr`c`]
      \\ simp[Abbr`b`]
      \\ qmatch_goalsub_abbrev_tac`evcn b _`
      \\ simp[Abbr`a0`]
      \\ ntac 2 (pop_assum mp_tac)
      \\ simp[restrict_def]
      \\ qmatch_goalsub_abbrev_tac`encode_set s`
      \\ `s ∈ fp`
      by (
        simp[Abbr`s`, Abbr`fp`, fn_partition_def]
        \\ simp[three_def, PULL_EXISTS, EXISTS_PROD]
        \\ metis_tac[])
      \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
      \\ simp[Abbr`s`]
      \\ qmatch_goalsub_abbrev_tac`encode_set s`
      \\ `s ∈ fp`
      by (
        simp[Abbr`s`, Abbr`fp`, fn_partition_def]
        \\ simp[three_def, PULL_EXISTS, EXISTS_PROD]
        \\ metis_tac[])
      \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
      \\ simp[Abbr`s`]
      \\ qmatch_goalsub_abbrev_tac`q f1`
      \\ `q f1 ∈ f1` by metis_tac[is_repfn_def]
      \\ strip_tac
      \\ qmatch_goalsub_abbrev_tac`q f2`
      \\ `q f2 ∈ f2` by metis_tac[is_repfn_def]
      \\ strip_tac
      \\ `f1 ⊆ three.agent` by simp[SUBSET_DEF, Abbr`f1`, Abbr`f`, fn_part_def]
      \\ `f2 ⊆ three.agent` by simp[SUBSET_DEF, Abbr`f2`, Abbr`f`, fn_part_def]
      \\ `q f1 ∈ three.agent ∧ q f2 ∈ three.agent` by metis_tac[SUBSET_DEF]
      \\ `b ∈ three.env ∧ d ∈ three.env`
      by (
        ntac 2 (pop_assum mp_tac)
        \\ simp[three_def, EXISTS_PROD, Abbr`b`, Abbr`d`]
        \\ rpt strip_tac \\ simp[] )
      \\ rpt conj_tac \\ irule(SIMP_RULE(srw_ss())[]evcn_in)
      \\ ntac 2 (pop_assum mp_tac)
      \\ simp[three_def]
      \\ PROVE_TAC[])
    \\ simp[ext0_three_eval]
    \\ simp[external_eval]
    \\ rpt gen_tac
    \\ qmatch_goalsub_abbrev_tac`encode_set (ft _)`
    \\ strip_tac
    \\ `∃f0 f1. f = f0::f1::[] ∧ f0 ∈ {#"0";#"1"} ∧ f1 ∈ {#"0";#"1"}`
    by (
      qpat_x_assum`f ∈ _`mp_tac
      \\ simp[ext0_three_env_eq]
      \\ strip_tac \\ simp[] )
    \\ simp[]
    \\ qmatch_goalsub_abbrev_tac`ft p`
    \\ `p ∈ three.agent`
    by ( simp[Abbr`p`, three_def] \\ fs[] )
    \\ `ft p ∈ fp`
    by ( simp[Abbr`fp`, fn_partition_def] \\ metis_tac[] )
    \\ qpat_x_assum`a ∈ _`mp_tac
    \\ simp[external_def, cf_external_def]
    \\ simp[repfns_def] \\ strip_tac
    \\ simp[]
    \\ simp[Once restrict_def]
    \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
    \\ qunabbrev_tac`p`
    \\ qmatch_goalsub_abbrev_tac`encode_set (ft p)`
    \\ `p ∈ three.agent`
    by ( simp[Abbr`p`, three_def] \\ fs[] )
    \\ `ft p ∈ fp`
    by ( simp[Abbr`fp`, fn_partition_def] \\ metis_tac[] )
    \\ simp[Once restrict_def]
    \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
    \\ qunabbrev_tac`p`
    \\ simp[Once restrict_def]
    \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
    \\ qmatch_goalsub_abbrev_tac`encode_set (ft p)`
    \\ `p ∈ three.agent`
    by ( simp[Abbr`p`, three_def] \\ fs[] )
    \\ `ft p ∈ fp`
    by ( simp[Abbr`fp`, fn_partition_def] \\ metis_tac[] )
    \\ simp[Once restrict_def]
    \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
    \\ qunabbrev_tac`p`
    \\ simp[Once restrict_def]
    \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
    \\ qmatch_goalsub_abbrev_tac`f0::f1::f2::[]`
    \\ simp[three_eval]
    \\ qmatch_goalsub_abbrev_tac`q ft0 ∈ _`
    \\ `q ft0 ∈ ft0` by metis_tac[is_repfn_def]
    \\ `ft0 ⊆ three.agent` by simp[Abbr`ft0`, Abbr`ft`, SUBSET_DEF, fn_part_def]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[]
      \\ conj_tac >- metis_tac[SUBSET_DEF]
      \\ qpat_x_assum`f1 ∈ _`mp_tac
      \\ simp[three_def]
      \\ PROVE_TAC[])
    \\ `FST (decode_pair (q ft0)) = [f0]`
    by (
      qmatch_goalsub_abbrev_tac`decode_pair p`
      \\ qpat_x_assum`p ∈ _`mp_tac
      \\ simp[Abbr`ft0`, Abbr`ft`]
      \\ simp[fn_part_def]
      \\ simp[three_eval_b3_part_0]
      \\ DEP_REWRITE_TAC[b3_where_inj]
      \\ qpat_x_assum`p ∈ _ ∧ _`strip_assume_tac
      \\ qpat_x_assum`p ∈ _`mp_tac
      \\ simp[three_def, PULL_EXISTS, EXISTS_PROD]
      \\ rpt gen_tac
      \\ simp[CONJ_ASSOC]
      \\ disch_then (mp_tac o CONJUNCT1)
      \\ rw[] \\ rw[])
    \\ simp[]
    \\ conj_asm1_tac
    >- (
      simp[evcn_def]
      \\ qpat_x_assum`f1 ∈ _`mp_tac
      \\ simp[]
      \\ strip_tac \\ simp[] )
    \\ simp[]
    \\ qpat_x_assum`Abbrev(f2 = _)`mp_tac
    \\ qho_match_abbrev_tac`(Abbrev(f2 = EL _ ((fx ("0","0") #"0") :: _))) ⇒ _`
    \\ simp[]
    \\ qabbrev_tac`fxx = λd0 d2. fx ([d0], "0") d2`
    \\ simp[]
    \\ simp[EL_4]
    \\ strip_tac
    \\ simp[Abbr`f2`]
    \\ simp[Abbr`fxx`, Abbr`fx`])
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu, Abbr`g`, b3_part_partitions]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ conj_asm1_tac
    >- (
      simp[ext0_three_def, PULL_EXISTS, EXISTS_PROD]
      \\ simp[external_def, cf_external_def, PULL_EXISTS, EXISTS_PROD]
      \\ qx_genl_tac[`d1`,`d0`] \\ strip_tac
      \\ qexists_tac`FST (decode_pair (CHOICE d0))`
      \\ simp[]
      \\ qpat_x_assum`d0 ∈ _`mp_tac
      \\ simp[Abbr`fp`, fn_partition_def]
      \\ strip_tac
      \\ `CHOICE d0 ∈ d0`
      by (
        irule CHOICE_DEF
        \\ simp[GSYM MEMBER_NOT_EMPTY]
        \\ simp[fn_part_def]
        \\ qexists_tac`x` \\ simp[] )
      \\ `d0 ⊆ three.agent`
      by simp[fn_part_def, SUBSET_DEF]
      \\ `CHOICE d0 ∈ three.agent` by metis_tac[SUBSET_DEF]
      \\ pop_assum mp_tac
      \\ simp_tac(srw_ss())[three_def, PULL_EXISTS, EXISTS_PROD]
      \\ qpat_x_assum`d1 ∈ _`mp_tac
      \\ simp_tac(srw_ss())[three_def]
      \\ simp[evcn_def]
      \\ rw[] )
    \\ conj_asm1_tac
    >- (
      simp[external_def, cf_external_def]
      \\ rpt strip_tac
      \\ DEP_REWRITE_TAC[encode_repfn_in_repfns]
      \\ simp[]
      \\ conj_asm1_tac
      >- simp[extensional_def]
      \\ simp[is_repfn_def]
      \\ gen_tac \\ strip_tac
      \\ `CHOICE s ∈ s`
      by (
        irule CHOICE_DEF
        \\ simp[GSYM MEMBER_NOT_EMPTY]
        \\ pop_assum mp_tac
        \\ simp[Abbr`fp`, fn_partition_def, PULL_EXISTS]
        \\ rpt strip_tac
        \\ simp[fn_part_def]
        \\ qexists_tac`x` \\ simp[] )
      \\ `s ⊆ three.agent`
      by (
        fs[Abbr`fp`, fn_partition_def]
        \\ simp[fn_part_def, SUBSET_DEF] )
      \\ `CHOICE s ∈ three.agent` by metis_tac[SUBSET_DEF]
      \\ qmatch_goalsub_abbrev_tac`decode_pair p`
      \\ qpat_x_assum`s ∈ fp`mp_tac
      \\ simp[Abbr`fp`, fn_partition_def]
      \\ strip_tac
      \\ qmatch_goalsub_abbrev_tac`pa ∈ s`
      \\ `pa ∈ three.agent`
      by (
        simp[Abbr`pa`, three_def]
        \\ qpat_x_assum`p ∈ _`mp_tac
        \\ simp[three_def, PULL_EXISTS, EXISTS_PROD]
        \\ rpt gen_tac \\ disch_then assume_tac
        \\ simp[unevcn_def]
        \\ metis_tac[])
      \\ qpat_x_assum`p ∈ s`mp_tac
      \\ simp[fn_part_def]
      \\ simp[three_eval_b3_part_0]
      \\ rpt strip_tac
      \\ DEP_REWRITE_TAC[b3_where_inj]
      \\ simp[Abbr`pa`]
      \\ qpat_x_assum`p ∈ _`mp_tac
      \\ simp[three_def, PULL_EXISTS, EXISTS_PROD]
      \\ rw[] \\ rw[])
    \\ simp[ext0_three_eval]
    \\ simp[external_eval]
    \\ simp[external_def, cf_external_def, PULL_EXISTS, EXISTS_PROD]
    \\ qx_genl_tac[`a`,`e`,`s`] \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`encode_repfn fp q`
    \\ first_x_assum(qspec_then`a`mp_tac)
    \\ simp[external_def, cf_external_def]
    \\ DEP_REWRITE_TAC[encode_repfn_in_repfns]
    \\ simp[]
    \\ conj_asm1_tac >- simp[extensional_def, Abbr`q`]
    \\ strip_tac
    \\ simp[encode_repfn_def]
    \\ simp[restrict_def]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum kall_tac
    \\ simp[three_eval]
    \\ `q s ∈ s` by metis_tac[is_repfn_def]
    \\ `s ⊆ three.agent`
    by (
      qpat_x_assum`s ∈ _`mp_tac
      \\ simp[Abbr`fp`, fn_partition_def, PULL_EXISTS, fn_part_def, SUBSET_DEF])
    \\ reverse IF_CASES_TAC >- metis_tac[SUBSET_DEF]
    \\ `CHOICE s ∈ s`
    by (
      irule CHOICE_DEF
      \\ simp[GSYM MEMBER_NOT_EMPTY]
      \\ qpat_x_assum`s ∈ _`mp_tac
      \\ simp[Abbr`fp`, fn_partition_def, PULL_EXISTS]
      \\ rpt strip_tac
      \\ simp[fn_part_def]
      \\ qexists_tac`x` \\ simp[] )
    \\ simp[Abbr`q`]
    \\ qmatch_goalsub_abbrev_tac`decode_pair p`
    \\ `p ∈ three.agent` by metis_tac[SUBSET_DEF]
    \\ pop_assum mp_tac
    \\ qpat_x_assum`a ∈ _`mp_tac
    \\ qpat_x_assum`e ∈ _`mp_tac
    \\ simp[ext0_three_agent_eq, three_def, PULL_EXISTS, EXISTS_PROD]
    \\ rpt strip_tac \\ rpt BasicProvers.VAR_EQ_TAC
    \\ simp[evcn_def, unevcn_def])
  \\ qpat_assum`h :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`g :- _ → _ -: _` o mp_then Any strip_assume_tac)
  \\ qpat_assum`g :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`h :- _ → _ -: _` o mp_then Any strip_assume_tac)
  \\ simp[homotopic_id_map_env_id]
  \\ simp[restrict_def]
  \\ conj_tac
  >- (
    simp[external_eval]
    \\ rpt gen_tac \\ strip_tac
    \\ irule EQ_SYM
    \\ IF_CASES_TAC \\ simp[]
    \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ simp[Abbr`h`, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ ntac 2 (pop_assum kall_tac)
    \\ simp[Abbr`g`, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ qmatch_goalsub_abbrev_tac`three.eval f1 _ = _ f2 _`
    \\ `f1 = f2`
    by (
      simp[Abbr`f1`, Abbr`f2`]
      \\ qpat_x_assum`e ∈ _`mp_tac
      \\ simp[external_def, cf_external_def, PULL_EXISTS, EXISTS_PROD]
      \\ rpt gen_tac \\ strip_tac
      \\ `CHOICE x ∈ x`
      by (
        irule CHOICE_DEF
        \\ simp[GSYM MEMBER_NOT_EMPTY]
        \\ qpat_x_assum`_ ∈ fp`mp_tac
        \\ simp[Abbr`fp`, fn_partition_def, PULL_EXISTS]
        \\ rpt strip_tac
        \\ simp[fn_part_def]
        \\ goal_assum(first_assum o mp_then Any mp_tac)
        \\ simp[])
      \\ `x ⊆ three.agent`
      by (
        fs[Abbr`fp`, fn_partition_def]
        \\ simp[fn_part_def, SUBSET_DEF] )
      \\ `CHOICE x ∈ three.agent` by metis_tac[SUBSET_DEF]
      \\ qmatch_goalsub_abbrev_tac`decode_pair p`
      \\ qpat_x_assum`x ∈ fp`mp_tac
      \\ simp[Abbr`fp`, fn_partition_def]
      \\ disch_then(qx_choose_then`b`strip_assume_tac)
      \\ qpat_x_assum`p ∈ x`mp_tac
      \\ simp[Once fn_part_def]
      \\ simp[three_eval_b3_part_0]
      \\ DEP_REWRITE_TAC[b3_where_inj]
      \\ conj_tac
      >- (
        simp[]
        \\ qpat_x_assum`b ∈ _`mp_tac
        \\ qpat_x_assum`p ∈ _`mp_tac
        \\ simp[three_def, PULL_EXISTS, EXISTS_PROD]
        \\ rpt strip_tac \\ rw[])
      \\ strip_tac
      \\ AP_TERM_TAC
      \\ AP_TERM_TAC
      \\ simp[fn_part_def, Once EXTENSION]
      \\ qx_gen_tac`z`
      \\ Cases_on`z ∈ three.agent` \\ simp[]
      \\ irule EQ_SYM
      \\ qmatch_goalsub_abbrev_tac`three.eval pp`
      \\ `pp ∈ three.agent`
      by (
        qpat_x_assum`p ∈ _`mp_tac
        \\ simp[Abbr`pp`, three_def, PULL_EXISTS, EXISTS_PROD]
        \\ rpt strip_tac \\ simp[] )
      \\ simp[three_eval_b3_part_0]
      \\ simp[Abbr`pp`]
      \\ metis_tac[] )
    \\ simp[Abbr`f2`]
    \\ pop_assum (SUBST_ALL_TAC o SYM)
    \\ simp[three_eval]
    \\ Cases_on`f1 ∈ three.agent` \\ simp[]
    \\ qpat_x_assum`e ∈ _`mp_tac
    \\ simp[external_def, cf_external_def, PULL_EXISTS, EXISTS_PROD]
    \\ rpt strip_tac
    \\ `x ⊆ three.agent`
    by (
      fs[Abbr`fp`, fn_partition_def]
      \\ simp[fn_part_def, SUBSET_DEF] )
    \\ `CHOICE x ∈ x`
    by (
      irule CHOICE_DEF
      \\ simp[GSYM MEMBER_NOT_EMPTY]
      \\ qpat_x_assum`_ ∈ fp`mp_tac
      \\ simp[Abbr`fp`, fn_partition_def, PULL_EXISTS]
      \\ rpt strip_tac
      \\ simp[fn_part_def]
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ simp[])
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ `CHOICE x ∈ three.agent` by metis_tac[SUBSET_DEF]
      \\ pop_assum mp_tac
      \\ qpat_x_assum`_ ∈ three.env`mp_tac
      \\ simp[evcn_def, three_def]
      \\ rw[] \\ rw[] )
    \\ simp[]
    \\ reverse conj_asm1_tac >- simp[]
    \\ fs[]
    \\ qpat_x_assum`a ∈ _`mp_tac
    \\ simp[external_def, cf_external_def]
    \\ simp[repfns_def] \\ strip_tac
    \\ simp[Abbr`f1`]
    \\ simp[restrict_def]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum kall_tac
    \\ qpat_x_assum`x ∈ _`mp_tac
    \\ simp[Abbr`fp`, fn_partition_def]
    \\ strip_tac
    \\ qmatch_asmsub_abbrev_tac`p ∈ x`
    \\ qmatch_goalsub_abbrev_tac`decode_pair qp`
    \\ qmatch_asmsub_abbrev_tac`is_repfn fp`
    \\ `x ∈ fp` by (simp[Abbr`fp`, fn_partition_def] \\ metis_tac[])
    \\ `qp ∈ x` by metis_tac[is_repfn_def]
    \\ qmatch_goalsub_abbrev_tac`evcn _ y`
    \\ qmatch_goalsub_abbrev_tac`evcn _ yy :: _`
    \\ `yy = y`
    by(
      rpt(qpat_x_assum`_ ∈ x`mp_tac)
      \\ simp[fn_part_def]
      \\ rpt strip_tac
      \\ ntac 2 (qhdtm_x_assum`$!`mp_tac)
      \\ simp[three_eval_b3_part_0]
      \\ DEP_REWRITE_TAC[b3_where_inj]
      \\ simp[]
      \\ ntac 3 (qpat_x_assum`_ ∈ three.agent`mp_tac)
      \\ simp[Ntimes three_def 3, PULL_EXISTS, EXISTS_PROD]
      \\ simp[Abbr`y`, Abbr`yy`]
      \\ rpt gen_tac \\ strip_tac \\ rpt BasicProvers.VAR_EQ_TAC \\ simp[]
      \\ rpt gen_tac \\ strip_tac \\ rpt BasicProvers.VAR_EQ_TAC \\ simp[]
      \\ rpt gen_tac \\ strip_tac \\ rpt BasicProvers.VAR_EQ_TAC \\ simp[]
      \\ srw_tac[SatisfySimps.SATISFY_ss][])
    \\ simp[]
    \\ irule EQ_SYM
    \\ irule evcn_idem
    \\ `qp ∈ three.agent` by metis_tac[SUBSET_DEF]
    \\ pop_assum mp_tac
    \\ simp[Abbr`y`]
    \\ simp[three_def, PULL_EXISTS]
    \\ rw[] \\ rw[])
  \\ simp[ext0_three_eval]
  \\ rpt gen_tac \\ strip_tac
  \\ irule EQ_SYM
  \\ IF_CASES_TAC \\ simp[]
  \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
  \\ pop_assum kall_tac
  \\ simp[Abbr`g`, mk_chu_morphism_def]
  \\ simp[restrict_def]
  \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
  \\ simp[Abbr`h`, mk_chu_morphism_def]
  \\ simp[restrict_def]
  \\ pop_assum kall_tac
  \\ qmatch_goalsub_abbrev_tac`encode_set (ft e0)`
  \\ `e0 ∈ three.agent`
  by (
    simp[three_def, Abbr`e0`]
    \\ qpat_x_assum`e ∈ _`mp_tac
    \\ simp[ext0_three_env_eq]
    \\ strip_tac \\ simp[] )
  \\ `ft e0 ∈ fp`
  by (
    simp[Abbr`fp`, fn_partition_def]
    \\ metis_tac[] )
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`d0::d1::_`
  \\ reverse conj_asm1_tac
  >- ( pop_assum SUBST1_TAC \\ simp[] )
  \\ `HD e = d0`
  by (
    simp[Abbr`d0`]
    \\ `CHOICE (ft e0) ∈ ft e0`
    by (
      irule CHOICE_DEF
      \\ simp[GSYM MEMBER_NOT_EMPTY]
      \\ simp[Abbr`ft`, fn_part_def]
      \\ qexists_tac`e0`
      \\ simp[] )
    \\ `ft e0 ⊆ three.agent`
    by simp[Abbr`ft`, fn_part_def, SUBSET_DEF]
    \\ qmatch_goalsub_abbrev_tac`decode_pair p`
    \\ `p ∈ three.agent` by metis_tac[SUBSET_DEF]
    \\ qpat_x_assum`p ∈ ft _`mp_tac
    \\ simp[Abbr`ft`, fn_part_def]
    \\ simp[three_eval_b3_part_0]
    \\ DEP_REWRITE_TAC[b3_where_inj]
    \\ simp[]
    \\ qpat_x_assum`_ ∈ three.agent`mp_tac
    \\ simp[three_def, PULL_EXISTS, EXISTS_PROD]
    \\ qpat_x_assum`_ ∈ three.agent`mp_tac
    \\ simp[three_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[Abbr`e0`]
    \\ strip_tac
    \\ rpt gen_tac \\ strip_tac \\ rpt BasicProvers.VAR_EQ_TAC \\ simp[])
  \\ `d1 = EL 1 e`
  by (
    qpat_x_assum`e ∈ _`mp_tac
    \\ simp[Abbr`d1`, ext0_three_env_eq]
    \\ strip_tac \\ simp[evcn_def] )
  \\ qpat_x_assum`e ∈ _`mp_tac
  \\ simp[ext0_three_env_eq]
  \\ strip_tac \\ fs[]
QED

val _ = export_theory();
