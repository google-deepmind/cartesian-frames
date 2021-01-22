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
  pairTheory pred_setTheory listTheory helperSetTheory categoryTheory
  cf0Theory cf1Theory cf2Theory cf4Theory cf5Theory cf6Theory cf7Theory cf8Theory

val _ = new_theory"cf9";

Definition cf_commit_def:
  cf_commit b c = mk_cf (c with agent := b)
End

Definition cf_commit_diff_def:
  cf_commit_diff b c = mk_cf (c with agent := c.agent DIFF b)
End

Theorem cf_commit_diff_cf_commit:
  cf_commit_diff b c = cf_commit (c.agent DIFF b) c
Proof
  rw[cf_commit_def, cf_commit_diff_def]
QED

Theorem cf_commit_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ b ⊆ c.agent ⇒
  cf_commit b c ∈ chu_objects w
Proof
  rw[cf_commit_def, in_chu_objects]
  \\ fs[wf_def, image_def, PULL_EXISTS, SUBSET_DEF, finite_cf_def]
  \\ metis_tac[SUBSET_DEF, SUBSET_FINITE]
QED

Theorem cf_commit_diff_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ b ⊆ c.agent ⇒
  cf_commit_diff b c ∈ chu_objects w
Proof
  rw[cf_commit_diff_cf_commit]
QED

Theorem cf_commit_additive_subagent:
  c ∈ chu_objects w ∧ b ⊆ c.agent ⇒
  additive_subagent (cf_commit b c) c
Proof
  rw[additive_subagent_committing]
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ qexistsl_tac[`c.env`,`c.eval`]
  \\ simp[cf_commit_def]
  \\ `c.world = w` by fs[in_chu_objects]
  \\ conj_tac \\ qmatch_goalsub_abbrev_tac`x ≃ y -: _`
  \\ `x ∈ chu_objects w ∧ y = x` suffices_by rw[]
  \\ simp[Abbr`x`, Abbr`y`, cf_component_equality]
  \\ fs[in_chu_objects, mk_cf_def, wf_def, finite_cf_def]
  \\ simp[image_def, SUBSET_DEF, PULL_EXISTS, FUN_EQ_THM]
  \\ metis_tac[SUBSET_DEF, SUBSET_FINITE]
QED

Theorem cf_commit_diff_additive_subagent:
  c ∈ chu_objects w ∧ b ⊆ c.agent ⇒
  additive_subagent (cf_commit_diff b c) c
Proof
  rw[cf_commit_diff_cf_commit]
  \\ irule cf_commit_additive_subagent
  \\ fs[SUBSET_DEF]
  \\ metis_tac[]
QED

Theorem is_brother_cf_commit_diff:
  c ∈ chu_objects w ∧ b ⊆ c.agent ⇒
  is_brother c (cf_commit b c) (cf_commit_diff b c)
Proof
  rw[is_brother_def]
  \\ qexists_tac`mk_cf <| world := w;
       agent := (sum (cf_commit b c) (cf_commit_diff b c)).agent;
       env := IMAGE (W (CURRY encode_pair)) c.env;
       eval := sum_eval c.eval c.eval |>`
  \\ qmatch_goalsub_abbrev_tac`c ≃ c' -: _`
  \\ `c.world = w` by fs[in_chu_objects]
  \\ `(cf_commit_diff b c).world = w ∧ (cf_commit b c).world = w`
  by simp[cf_commit_diff_def, cf_commit_def]
  \\ `c' ∈ chu_objects w`
  by (
    `sum (cf_commit b c) (cf_commit_diff b c) ∈ chu_objects w` by simp[]
    \\ fs[in_chu_objects, Abbr`c'`, wf_def, Excl"sum_in_chu_objects"]
    \\ fs[finite_cf_def, image_def, PULL_EXISTS, SUBSET_DEF]
    \\ rpt strip_tac
    \\ first_x_assum drule
    \\ simp[Once sum_def, EXISTS_PROD, PULL_EXISTS]
    \\ simp[Once cf_commit_def, Once cf_commit_diff_def]
    \\ disch_then drule \\ disch_then drule
    \\ simp[sum_def, mk_cf_def, PULL_EXISTS, cf_commit_def, cf_commit_diff_def]
    \\ rw[sum_eval_def] \\ rw[]
    \\ qpat_x_assum`a ∈ _` mp_tac
    \\ simp_tac(srw_ss())[sum_def, cf_commit_def, cf_commit_diff_def]
    \\ metis_tac[])
  \\ conj_tac
  >- (
    simp[homotopy_equiv_def]
    \\ qexists_tac`mk_chu_morphism c c' <|
         map_agent := λa. encode_sum ((if a ∈ b then INL else INR) a);
         map_env := FST o decode_pair |>`
    \\ qexists_tac`mk_chu_morphism c' c <|
         map_agent := λa. sum_CASE (decode_sum a) I I;
         map_env := W (CURRY encode_pair) |>`
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`c'`, mk_cf_def, PULL_EXISTS]
      \\ simp[sum_def, PULL_EXISTS, cf_commit_def, cf_commit_diff_def]
      \\ rw[sum_eval_def]
      \\ Cases_on`a ∈ b` \\ fs[])
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`c'`, mk_cf_def, PULL_EXISTS]
      \\ simp[sum_def, PULL_EXISTS, cf_commit_def, cf_commit_diff_def]
      \\ rw[sum_eval_def] \\ rw[]
      \\ rfs[SUBSET_DEF] )
    \\ simp[homotopic_id_map_env_id]
    \\ imp_res_tac compose_in_chu
    \\ simp[restrict_def, mk_chu_morphism_def]
    \\ rw[Abbr`c'`, mk_cf_def] \\ rw[] \\ fs[] )
  \\ simp[]
  \\ simp[is_subsum_def]
  \\ simp[Once sum_def]
  \\ conj_tac >- simp[Abbr`c'`]
  \\ conj_tac >- simp[Abbr`c'`]
  \\ conj_tac >- (
    simp[Abbr`c'`, sum_def]
    \\ simp[cf_commit_def, cf_commit_diff_def]
    \\ simp[SUBSET_DEF, PULL_EXISTS] )
  \\ conj_tac >- (
    simp[Abbr`c'`, restrict_def, mk_cf_def, sum_def,
         PULL_EXISTS, EXISTS_PROD, cf_commit_def, cf_commit_diff_def]
    \\ rw[sum_eval_def, FUN_EQ_THM]
    \\ rw[] \\ rw[] \\ gs[] )
  \\ qmatch_goalsub_abbrev_tac`cf_commit b c ≃ c1 -: _`
  \\ qmatch_goalsub_abbrev_tac`cf_commit_diff b c ≃ c2 -: _`
  \\ `c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w`
  by (
    fs[in_chu_objects, Abbr`c1`, Abbr`c2`]
    \\ fs[wf_def, finite_cf_def]
    \\ simp[image_def, SUBSET_DEF, PULL_EXISTS]
    \\ simp[cf_commit_def, cf_commit_diff_def, sum_def, Abbr`c'`]
    \\ metis_tac[SUBSET_FINITE] )
  \\ conj_tac >- (
    simp[homotopy_equiv_def]
    \\ qexists_tac`mk_chu_morphism (cf_commit b c) c1 <|
         map_agent := encode_sum o INL;
         map_env := FST o decode_pair |>`
    \\ qexists_tac`mk_chu_morphism c1 (cf_commit b c) <|
         map_agent := OUTL o decode_sum;
         map_env := W (CURRY encode_pair) |>`
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`c1`, cf_commit_def, mk_cf_def]
      \\ simp[Abbr`c'`, PULL_EXISTS, mk_cf_def]
      \\ simp[sum_def, sum_eval_def, cf_commit_def] )
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`c1`, cf_commit_def, mk_cf_def, PULL_EXISTS]
      \\ simp[Abbr`c'`, PULL_EXISTS, mk_cf_def]
      \\ simp[sum_def, sum_eval_def, cf_commit_def] )
    \\ simp[homotopic_id_map_agent_id]
    \\ imp_res_tac compose_in_chu
    \\ simp[restrict_def, mk_chu_morphism_def]
    \\ simp[cf_commit_def, mk_cf_def, PULL_EXISTS, FUN_EQ_THM, Abbr`c1`] )
  \\ simp[homotopy_equiv_def]
  \\ qexists_tac`mk_chu_morphism (cf_commit_diff b c) c2 <|
       map_agent := encode_sum o INR;
       map_env := FST o decode_pair |>`
  \\ qexists_tac`mk_chu_morphism c2 (cf_commit_diff b c) <|
       map_agent := OUTR o decode_sum;
       map_env := W (CURRY encode_pair) |>`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`c2`, cf_commit_diff_def, mk_cf_def]
    \\ simp[Abbr`c'`, PULL_EXISTS, mk_cf_def]
    \\ simp[sum_def, sum_eval_def, cf_commit_diff_def] )
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`c2`, cf_commit_diff_def, mk_cf_def, PULL_EXISTS]
    \\ simp[Abbr`c'`, PULL_EXISTS, mk_cf_def]
    \\ simp[sum_def, sum_eval_def, cf_commit_diff_def] )
  \\ simp[homotopic_id_map_agent_id]
  \\ imp_res_tac compose_in_chu
  \\ simp[restrict_def, mk_chu_morphism_def]
  \\ simp[cf_commit_diff_def, mk_cf_def, PULL_EXISTS, FUN_EQ_THM, Abbr`c2`]
QED

Definition cf_assume_def:
  cf_assume f c = mk_cf (c with env := f)
End

Definition cf_assume_diff_def:
  cf_assume_diff f c = mk_cf (c with env := c.env DIFF f)
End

(* TODO: example of cf_assume_diff for meteor example *)

Theorem swap_cf_assume:
  swap (cf_assume f c) = cf_commit f (swap c)
Proof
  simp[cf_assume_def, cf_commit_def, cf_component_equality]
  \\ simp[mk_cf_def, FUN_EQ_THM] \\ rw[] \\ fs[]
QED

Theorem swap_cf_assume_diff:
  swap (cf_assume_diff f c) = cf_commit_diff f (swap c)
Proof
  simp[cf_assume_diff_def, cf_commit_diff_def, cf_component_equality]
  \\ simp[mk_cf_def, FUN_EQ_THM] \\ rw[] \\ fs[]
QED

Theorem swap_cf_commit:
  swap (cf_commit b c) = cf_assume b (swap c)
Proof
  metis_tac[swap_swap, swap_cf_assume]
QED

Theorem swap_cf_commit_diff:
  swap (cf_commit_diff b c) = cf_assume_diff b (swap c)
Proof
  metis_tac[swap_swap, swap_cf_assume_diff]
QED

Theorem cf_assume_additive_subenvironment:
  c ∈ chu_objects w ∧ f ⊆ c.env ⇒
  additive_subenvironment c (cf_assume f c)
Proof
  rw[additive_subenvironment_def, swap_cf_assume]
  \\ irule cf_commit_additive_subagent
  \\ simp[] \\ metis_tac[]
QED

Theorem cf_assume_diff_additive_subenvironment:
  c ∈ chu_objects w ∧ f ⊆ c.env ⇒
  additive_subenvironment c (cf_assume_diff f c)
Proof
  rw[additive_subenvironment_def, swap_cf_assume_diff]
  \\ irule cf_commit_diff_additive_subagent
  \\ simp[] \\ metis_tac[]
QED

Definition partitions_def:
  partitions X Y ⇔ ∃R. R equiv_on Y ∧ X = partition R Y
End

Theorem partitions_thm:
  partitions X Y ⇔
  ((∀x. x ∈ X ⇒ x ≠ ∅ ∧ x ⊆ Y) ∧
   (∀y. y ∈ Y ⇒ ∃!x. x ∈ X ∧ y ∈ x))
Proof
  simp[partitions_def]
  \\ eq_tac \\ strip_tac
  >- (
    simp[partition_def]
    \\ conj_tac
    >- (
      CCONTR_TAC \\ fs[]
      \\ pop_assum mp_tac
      \\ simp[GSYM MEMBER_NOT_EMPTY, SUBSET_DEF]
      \\ metis_tac[equiv_on_def] )
    \\ rpt strip_tac
    \\ simp[EXISTS_UNIQUE_THM, PULL_EXISTS]
    \\ qexists_tac`y`
    \\ rw[]
    >- metis_tac[equiv_on_def]
    \\ metis_tac[equiv_class_eq])
  \\ fs[EXISTS_UNIQUE_ALT]
  \\ fs[Once (GSYM RIGHT_EXISTS_IMP_THM)]
  \\ fs[SKOLEM_THM]
  \\ qexists_tac`λy z. f y = f z`
  \\ simp[equiv_on_def]
  \\ conj_tac >- metis_tac[]
  \\ simp[partition_def, Once EXTENSION]
  \\ rw[EQ_IMP_THM]
  >- (
    `∃a. a ∈ x ∧ a ∈ Y` by metis_tac[MEMBER_NOT_EMPTY, SUBSET_DEF]
    \\ qexists_tac`a` \\ simp[]
    \\ `f a = x` by metis_tac[]
    \\ simp[EXTENSION]
    \\ metis_tac[SUBSET_DEF] )
  \\ `f y ∈ X ∧ y ∈ f y` by metis_tac[]
  \\ qmatch_goalsub_abbrev_tac`z ∈ X`
  \\ `z = f y` suffices_by rw[]
  \\ rw[Abbr`z`, EXTENSION]
  \\ reverse(Cases_on`x ∈ Y`) \\ simp[]
  >- metis_tac[SUBSET_DEF]
  \\ metis_tac[]
QED

Theorem partitions_FINITE:
  partitions X Y ∧ FINITE Y ⇒
  FINITE X ∧ EVERY_FINITE X
Proof
  rw[partitions_def]
  \\ metis_tac[FINITE_partition]
QED

Definition is_repfn_def:
  is_repfn X q ⇔
  extensional q X ∧ ∀x. x ∈ X ⇒ q x ∈ x
End

Definition encode_set_def:
  encode_set = encode_list o SET_TO_LIST
End

Definition decode_set_def:
  decode_set = set o decode_list
End

Theorem decode_encode_set[simp]:
  FINITE s ⇒ decode_set (encode_set s) = s
Proof
  rw[decode_set_def, encode_set_def, SET_TO_LIST_INV]
QED

Definition repfns_def:
  repfns b =
    { encode_function (IMAGE encode_set b)
        (restrict (q o decode_set) (IMAGE encode_set b))
      | q | is_repfn b q }
End

Theorem FINITE_repfns[simp]:
  FINITE b ∧ EVERY_FINITE b ⇒ FINITE (repfns b)
Proof
  rw[repfns_def]
  \\ qspec_then`λq. IMAGE (λx. (x, (decode_function q (encode_set x)))) b` irule FINITE_INJ
  \\ qexists_tac`b`
  \\ qexists_tac`{IMAGE (λx. (x, q x)) b | q | is_repfn b q}`
  \\ conj_tac
  >- (
    irule SUBSET_FINITE
    \\ qexists_tac`POW (b × BIGUNION b)`
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ simp[IN_POW, SUBSET_DEF, PULL_EXISTS]
    \\ simp[is_repfn_def]
    \\ metis_tac[] )
  \\ simp[INJ_DEF, PULL_EXISTS]
  \\ qho_match_abbrev_tac`(∀q. is_repfn b q ⇒ ∃q'. P q q') ∧ _`
  \\ `∀q. is_repfn b q ⇒ P q q`
  by (
    simp[Abbr`P`]
    \\ qx_gen_tac`q`
    \\ strip_tac
    \\ irule IMAGE_CONG
    \\ simp[restrict_def, PULL_EXISTS]
    \\ metis_tac[] )
  \\ fs[Abbr`P`]
  \\ conj_tac >- metis_tac[]
  \\ rw[Once EXTENSION, FORALL_PROD]
  \\ AP_TERM_TAC
  \\ simp[restrict_def, PULL_EXISTS, FUN_EQ_THM]
  \\ rw[] \\ simp[]
  \\ metis_tac[]
QED

Theorem repfns_empty[simp]:
  repfns ∅ = { encode_function ∅ (K ARB) }
Proof
  rw[SET_EQ_SUBSET, SUBSET_DEF]
  \\ gs[repfns_def]
  >- ( AP_TERM_TAC \\ rw[FUN_EQ_THM, restrict_def] )
  \\ qexists_tac`K ARB`
  \\ rw[is_repfn_def, extensional_def, restrict_def]
  \\ AP_TERM_TAC \\ rw[FUN_EQ_THM]
QED

Definition cf_external_def:
  cf_external b c = mk_cf <| world := c.world;
    agent := repfns b;
    env := IMAGE encode_pair (IMAGE encode_set b × c.env);
    eval := λq p. c.eval
      (decode_function q (FST (decode_pair p)))
      (SND (decode_pair p)) |>
End

Definition cf_external_mod_def:
  cf_external_mod b c = mk_cf <| world := c.world;
    agent := IMAGE encode_set b;
    env := IMAGE encode_pair (repfns b × c.env);
    eval := λa e. c.eval (decode_function (FST (decode_pair e)) a)
                         (SND (decode_pair e)) |>
End

Theorem cf_external_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ partitions b c.agent ⇒
  cf_external b c ∈ chu_objects w
Proof
  simp[in_chu_objects, cf_external_def]
  \\ strip_tac
  \\ fs[wf_def, finite_cf_def]
  \\ drule partitions_FINITE
  \\ rw[]
  \\ rw[image_def, SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
  \\ first_x_assum irule \\ rw[]
  \\ fs[repfns_def]
  \\ simp[restrict_def]
  \\ fs[is_repfn_def, partitions_thm]
  \\ metis_tac[SUBSET_DEF]
QED

Theorem cf_external_mod_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ partitions b c.agent ⇒
  cf_external_mod b c ∈ chu_objects w
Proof
  simp[in_chu_objects, cf_external_mod_def]
  \\ strip_tac
  \\ fs[wf_def, finite_cf_def]
  \\ drule partitions_FINITE
  \\ rw[]
  \\ rw[image_def, SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
  \\ first_x_assum irule \\ rw[]
  \\ fs[repfns_def]
  \\ simp[restrict_def]
  \\ fs[is_repfn_def, partitions_thm]
  \\ metis_tac[SUBSET_DEF]
QED

Theorem is_sister_cf_external_mod:
  c ∈ chu_objects w ∧ partitions b c.agent ⇒
  is_sister c (cf_external b c) (cf_external_mod b c)
Proof
  rw[is_sister_def]
  \\ `c.world = w` by fs[in_chu_objects]
  \\ `∀e. e ∈ c.env ⇒
        (mk_chu_morphism (cf_external b c) (swap (cf_external_mod b c)) <|
         map_agent := λq. encode_pair (q, e);
         map_env := λx. encode_pair (x, e) |>)
          :- cf_external b c → (swap (cf_external_mod b c)) -: chu w`
  by (
    rw[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[cf_external_def, cf_external_mod_def, mk_cf_def] )
  \\ pop_assum mp_tac
  \\ qho_match_abbrev_tac`(∀e. e ∈ c.env ⇒ h e :- _ → _ -: _) ⇒ _`
  \\ strip_tac
  \\ qexists_tac`mk_cf <| world := w;
       agent := IMAGE encode_pair (repfns b × IMAGE encode_set b);
       env := IMAGE (encode_morphism o h) c.env;
       eval := λp e. (cf_external b c).eval (FST (decode_pair p))
                     ((decode_morphism (cf_external b c) (swap (cf_external_mod b c)) e).map.map_env (SND (decode_pair p))) |>`
  \\ qmatch_goalsub_abbrev_tac`c ≃ d -: _`
  \\ `d ∈ chu_objects w`
  by (
    simp[in_chu_objects, Abbr`d`]
    \\ reverse conj_tac
    >- (
      simp[finite_cf_def]
      \\ drule partitions_FINITE
      \\ imp_res_tac in_chu_objects_finite_world
      \\ fs[in_chu_objects, wf_def, finite_cf_def] )
    \\ simp[SUBSET_DEF, image_def, PULL_EXISTS, EXISTS_PROD]
    \\ rpt strip_tac
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[]
    \\ `cf_external b c ∈ chu_objects w` by simp[]
    \\ fs[in_chu_objects, wf_def] \\ fs[]
    \\ first_x_assum irule
    \\ simp[cf_external_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[Abbr`h`, mk_chu_morphism_def, restrict_def]
    \\ simp[cf_external_mod_def]
    \\ metis_tac[])
  \\ `FINITE b ∧ EVERY_FINITE b` by (
    drule partitions_FINITE
    \\ metis_tac[in_chu_objects, wf_def, finite_cf_def] )
  \\ `(cf_external b c).world = w` by simp[cf_external_def]
  \\ `SURJ (encode_morphism o h) c.env d.env`
  by (
    simp[SURJ_DEF, mk_chu_morphism_def, restrict_def]
    \\ simp[Abbr`d`, PULL_EXISTS]
    \\ metis_tac[] )
  \\ `b ≠ ∅ ⇒ INJ (encode_morphism o h) c.env d.env`
  by (
    strip_tac
    \\ simp[INJ_DEF]
    \\ conj_tac >- fs[SURJ_DEF]
    \\ simp[mk_chu_morphism_def, restrict_def]
    \\ rpt gen_tac \\ strip_tac
    \\ disch_then(mp_tac o Q.AP_TERM`decode_morphism (cf_external b c) (swap (cf_external_mod b c))`)
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[]
    \\ simp[Abbr`h`, morphism_component_equality]
    \\ simp[mk_chu_morphism_def, restrict_def]
    \\ simp[cf_external_def, cf_external_mod_def]
    \\ rw[FUN_EQ_THM]
    \\ fs[GSYM MEMBER_NOT_EMPTY]
    \\ qmatch_assum_rename_tac`z ∈ b`
    \\ first_x_assum(qspec_then`encode_set z`mp_tac)
    \\ reverse IF_CASES_TAC >- metis_tac[] \\ simp[] )
  \\ conj_asm1_tac
  >- (
    simp[homotopy_equiv_def]
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`mk_chu_morphism d c <|
         map_agent := λp. decode_function (FST (decode_pair p)) (SND (decode_pair p));
         map_env := encode_morphism o h |>`
    \\ qmatch_goalsub_abbrev_tac`k o _ -: _`
    \\ qexists_tac`mk_chu_morphism c d <|
         map_agent := λa. @b. b ∈ d.agent ∧ k.map.map_agent b = a;
         map_env := λe. @f. f ∈ c.env ∧ k.map.map_env f = e |>`
    \\ qmatch_goalsub_abbrev_tac`_ o j -: _`
    \\ simp[]
    \\ `SURJ k.map.map_agent d.agent c.agent`
    by (
      simp[Abbr`d`, SURJ_DEF, Abbr`k`, PULL_EXISTS,
           mk_chu_morphism_def, EXISTS_PROD, restrict_def]
      \\ simp[repfns_def, PULL_EXISTS]
      \\ conj_tac
      >- (
        rpt strip_tac
        \\ DEP_REWRITE_TAC[decode_encode_function]
        \\ simp[]
        \\ simp[restrict_def]
        \\ fs[is_repfn_def, partitions_thm]
        \\ metis_tac[SUBSET_DEF] )
      \\ rpt strip_tac
      \\ qunabbrev_tac`j`
      \\ `∃!s. s ∈ b ∧ x ∈ s` by metis_tac[partitions_thm]
      \\ fs[EXISTS_UNIQUE_ALT]
      \\ qexists_tac`s`
      \\ qexists_tac`λz. if z = s then x else if z ∈ b then CHOICE z else ARB`
      \\ conj_asm1_tac
      >- (
        simp[is_repfn_def, extensional_def]
        \\ metis_tac[CHOICE_DEF, partitions_thm] )
      \\ conj_asm1_tac >- metis_tac[]
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ pop_assum kall_tac
      \\ simp[restrict_def]
      \\ metis_tac[] )
    \\ simp[Once CONJ_COMM, GSYM CONJ_ASSOC]
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu, Abbr`k`]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`d`, PULL_EXISTS, EXISTS_PROD, mk_cf_def]
      \\ conj_tac >- metis_tac[]
      \\ conj_asm1_tac
      >- (
        simp[repfns_def, PULL_EXISTS]
        \\ simp[restrict_def]
        \\ simp[is_repfn_def]
        \\ PROVE_TAC[partitions_thm, SUBSET_DEF] )
      \\ rpt strip_tac
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ pop_assum kall_tac
      \\ qunabbrev_tac`j`
      \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
      \\ simp[]
      \\ simp[Abbr`h`, mk_chu_morphism_def, restrict_def]
      \\ simp[cf_external_mod_def]
      \\ simp[cf_external_def, mk_cf_def]
      \\ metis_tac[] )
    \\ simp[Once CONJ_COMM, CONJ_ASSOC]
    \\ simp[GSYM CONJ_ASSOC]
    \\ `SURJ k.map.map_env c.env d.env`
    by (
      fs[SURJ_DEF, Abbr`k`, mk_chu_morphism_def, restrict_def]
      \\ metis_tac[] )
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[Abbr`j`]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ conj_tac >- metis_tac[SURJ_DEF]
      \\ conj_tac >- metis_tac[SURJ_DEF]
      \\ rpt gen_tac \\ strip_tac
      \\ SELECT_ELIM_TAC
      \\ conj_tac >- metis_tac[SURJ_DEF]
      \\ rpt gen_tac \\ strip_tac
      \\ SELECT_ELIM_TAC
      \\ conj_tac >- metis_tac[SURJ_DEF]
      \\ rpt gen_tac \\ strip_tac
      \\ BasicProvers.VAR_EQ_TAC
      \\ BasicProvers.VAR_EQ_TAC
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ simp[homotopic_id_map_env_id]
    \\ qpat_assum`k :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then(qpat_assum`j :- _ → _ -: _` o mp_then Any strip_assume_tac)
    \\ qpat_assum`j :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then(qpat_assum`k :- _ → _ -: _` o mp_then Any strip_assume_tac)
    \\ simp[restrict_def]
    \\ simp[Abbr`j`, mk_chu_morphism_def, restrict_def]
    \\ ntac 3 (pop_assum kall_tac)
    \\ reverse conj_tac >- metis_tac[SURJ_DEF]
    \\ rpt strip_tac
    \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ reverse(Cases_on`a ∈ c.agent`)
    >- metis_tac[in_chu_objects, wf_def]
    \\ `b ≠ ∅` by (
      metis_tac[partitions_thm, MEMBER_NOT_EMPTY, EXISTS_UNIQUE_THM] )
    \\ `INJ k.map.map_env c.env d.env`
    by (
      fs[INJ_DEF, Abbr`k`, mk_chu_morphism_def, restrict_def]
      \\ metis_tac[] )
    \\ metis_tac[INJ_DEF])
  \\ reverse conj_tac >- simp[cf_external_def, cf_external_mod_def]
  \\ simp[is_subtensor_def]
  \\ `d.world = w` by metis_tac[homotopy_equiv_def, maps_to_in_chu, in_chu_objects]
  \\ `(cf_external_mod b c).world = w` by simp[cf_external_mod_def]
  \\ simp[Once tensor_def]
  \\ conj_tac
  >- (
    simp[Once tensor_def, Abbr`d`]
    \\ simp[cf_external_def, cf_external_mod_def] )
  \\ conj_tac
  >- (
    simp[tensor_def, Abbr`d`, SUBSET_DEF, hom_def, PULL_EXISTS]
    \\ metis_tac[] )
  \\ conj_tac
  >- (
    simp[tensor_def, Abbr`d`, mk_cf_def, restrict_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[FUN_EQ_THM]
    \\ rpt gen_tac
    \\ irule EQ_SYM
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ simp[Once cf_external_def]
    \\ simp[Once cf_external_mod_def, hom_def]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum strip_assume_tac
    \\ BasicProvers.VAR_EQ_TAC
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ metis_tac[] )
  \\ qmatch_goalsub_abbrev_tac`cf_external b c ≃ e1 -: _`
  \\ qmatch_goalsub_abbrev_tac`cf_external_mod b c ≃ e2 -: _`
  \\ Cases_on`b = ∅` >- (
    simp[cf_external_def, cf_external_mod_def, Abbr`e1`, Abbr`e2`]
    \\ qmatch_goalsub_abbrev_tac`x ≃ y -: _`
    \\ conj_asm1_tac
    >- (
      simp[homotopy_equiv_def]
      \\ qexists_tac`mk_chu_morphism x y <| map_agent := I; map_env := K ARB |>`
      \\ qexists_tac`mk_chu_morphism y x <| map_agent := I; map_env := K ARB |>`
      \\ conj_asm1_tac
      >- (
        simp[maps_to_in_chu, is_chu_morphism_def, mk_chu_morphism_def]
        \\ simp[restrict_def]
        \\ simp[Abbr`x`, Abbr`y`]
        \\ simp[in_chu_objects, finite_cf_def]
        \\ imp_res_tac in_chu_objects_finite_world
        \\ simp[image_def] )
      \\ `x ∈ chu_objects w ∧ y ∈ chu_objects w` by metis_tac[maps_to_in_chu]
      \\ conj_asm1_tac
      >- (
        simp[maps_to_in_chu, is_chu_morphism_def, mk_chu_morphism_def]
        \\ simp[restrict_def]
        \\ simp[Abbr`x`, Abbr`y`] )
      \\ simp[homotopic_id_map_agent_id]
      \\ imp_res_tac compose_in_chu
      \\ simp[restrict_def, mk_chu_morphism_def]
      \\ simp[Abbr`x`, Abbr`y`] )
    \\ qmatch_goalsub_abbrev_tac`x' ≃ y' -: _`
    \\ Cases_on`c.env = ∅`
    >- (
      `x' = null w ∧ y' = null w`
      by (
        simp[Abbr`x'`, Abbr`y'`, cf_component_equality, Abbr`d`]
        \\ simp[mk_cf_def, FUN_EQ_THM] )
      \\ imp_res_tac in_chu_objects_finite_world
      \\ simp[] )
    \\ qpat_x_assum`c ≃ d -: _`mp_tac
    \\ simp[homotopy_equiv_def]
    \\ disch_then(qx_choosel_then[`f`,`g`]strip_assume_tac)
    \\ qexists_tac`mk_chu_morphism x' y' <| map_agent := I;
         map_env := encode_pair o pair$## I f.map.map_env o decode_pair |>`
    \\ qexists_tac`mk_chu_morphism y' x' <| map_agent := I;
         map_env := encode_pair o pair$## I g.map.map_env o decode_pair |>`
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu, is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`x'`, Abbr`y'`, PULL_EXISTS, EXISTS_PROD]
      \\ simp[in_chu_objects, finite_cf_def]
      \\ imp_res_tac in_chu_objects_finite_world
      \\ simp[image_def]
      \\ metis_tac[maps_to_in_chu, in_chu_objects,
                   is_chu_morphism_def, wf_def, finite_cf_def])
    \\ `x' ∈ chu_objects w ∧ y' ∈ chu_objects w` by metis_tac[maps_to_in_chu]
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu, is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`x'`, Abbr`y'`, PULL_EXISTS, EXISTS_PROD]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def])
    \\ simp[homotopic_id_map_agent_id]
    \\ imp_res_tac compose_in_chu
    \\ simp[restrict_def, mk_chu_morphism_def]
    \\ simp[Abbr`x'`, Abbr`y'`] )
  \\ `BIJ (encode_morphism o h) c.env d.env`
  by metis_tac[BIJ_DEF]
  \\ qmatch_assum_abbrev_tac`BIJ he _ _`
  \\ conj_tac
  >- (
    simp[homotopy_equiv_def]
    \\ qexists_tac`mk_chu_morphism (cf_external b c) e1 <| map_agent := I;
         map_env := encode_pair o pair$## I (LINV he c.env)
                    o decode_pair |>`
    \\ qexists_tac`mk_chu_morphism e1 (cf_external b c) <| map_agent := I;
         map_env := encode_pair o pair$## I he o decode_pair |>`
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ conj_tac
      >- (
        simp[in_chu_objects, Abbr`e1`]
        \\ imp_res_tac in_chu_objects_finite_world
        \\ simp[finite_cf_def]
        \\ simp[image_def, PULL_EXISTS, SUBSET_DEF, EXISTS_PROD]
        \\ simp[Abbr`d`, PULL_EXISTS, mk_cf_def]
        \\ reverse conj_tac
        >- metis_tac[cf_external_in_chu_objects, cf_external_mod_in_chu_objects,
                     in_chu_objects, wf_def, finite_cf_def, IMAGE_FINITE]
        \\ simp[Once cf_external_def, Once cf_external_mod_def, PULL_EXISTS]
        \\ rpt gen_tac \\ strip_tac
        \\ reverse IF_CASES_TAC >- metis_tac[]
        \\ simp[Abbr`he`]
        \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
        \\ conj_tac >- metis_tac[]
        \\ `(cf_external b c) ∈ chu_objects w` by simp[]
        \\ pop_assum mp_tac \\ simp[in_chu_objects,Excl"cf_external_in_chu_objects"]
        \\ simp[wf_def]
        \\ strip_tac
        \\ first_x_assum irule
        \\ simp[Once cf_external_def]
        \\ `is_chu_morphism (cf_external b c) (swap (cf_external_mod b c)) (h x).map` by metis_tac[maps_to_in_chu]
        \\ pop_assum mp_tac \\ simp[is_chu_morphism_def]
        \\ strip_tac
        \\ first_x_assum irule
        \\ simp[cf_external_mod_def])
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`e1`, mk_cf_def, PULL_EXISTS, EXISTS_PROD]
      \\ simp[Abbr`d`, PULL_EXISTS, mk_cf_def]
      \\ conj_tac
      >- (simp[cf_external_mod_def, cf_external_def] \\ metis_tac[BIJ_LINV_THM])
      \\ rpt strip_tac
      \\ reverse IF_CASES_TAC
      >- (gs[cf_external_mod_def, cf_external_def] \\ metis_tac[])
      \\ drule BIJ_LINV_THM
      \\ simp[] \\ strip_tac
      \\ simp[Abbr`he`]
      \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
      \\ simp[Abbr`h`, mk_chu_morphism_def, restrict_def] )
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ conj_tac >- metis_tac[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`e1`, PULL_EXISTS, EXISTS_PROD, mk_cf_def]
      \\ simp[Once cf_external_def, PULL_EXISTS, EXISTS_PROD]
      \\ simp[Once cf_external_mod_def]
      \\ conj_tac >- metis_tac[INJ_DEF]
      \\ simp[Once cf_external_def, PULL_EXISTS, EXISTS_PROD, SimpR``(/\)``]
      \\ simp[PULL_EXISTS]
      \\ simp[Abbr`d`, mk_cf_def, PULL_EXISTS]
      \\ simp[Once cf_external_def]
      \\ rpt gen_tac \\ strip_tac
      \\ simp[Once cf_external_mod_def]
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ simp[Abbr`he`]
      \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
      \\ simp[Abbr`h`, mk_chu_morphism_def, restrict_def]
      \\ simp[Once cf_external_mod_def])
    \\ `e1 ∈ chu_objects w` by metis_tac[maps_to_in_chu]
    \\ simp[homotopic_id_map_agent_id]
    \\ imp_res_tac compose_in_chu
    \\ simp[mk_chu_morphism_def, restrict_def]
    \\ simp[Abbr`e1`] )
  \\ `e2 ∈ chu_objects w`
  by (
    simp[Abbr`e2`, in_chu_objects]
    \\ imp_res_tac in_chu_objects_finite_world
    \\ simp[finite_cf_def]
    \\ simp[image_def, PULL_EXISTS, SUBSET_DEF, EXISTS_PROD]
    \\ simp[Abbr`d`, PULL_EXISTS, mk_cf_def]
    \\ reverse conj_tac
    >- metis_tac[cf_external_in_chu_objects, cf_external_mod_in_chu_objects,
                 in_chu_objects, wf_def, finite_cf_def, IMAGE_FINITE]
    \\ simp[Once cf_external_def, Once cf_external_mod_def, PULL_EXISTS]
    \\ rpt gen_tac \\ strip_tac
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ simp[Abbr`he`]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ conj_tac >- metis_tac[]
    \\ `(cf_external b c) ∈ chu_objects w` by simp[]
    \\ pop_assum mp_tac \\ simp[in_chu_objects,Excl"cf_external_in_chu_objects"]
    \\ simp[wf_def]
    \\ strip_tac
    \\ first_x_assum irule
    \\ simp[Once cf_external_def]
    \\ simp[Abbr`h`, mk_chu_morphism_def, restrict_def]
    \\ simp[cf_external_def, cf_external_mod_def]
    \\ metis_tac[])
  \\ simp[homotopy_equiv_def]
  \\ qexists_tac`mk_chu_morphism (cf_external_mod b c) e2 <| map_agent := I;
       map_env := encode_pair o pair$## I (LINV he c.env)
                  o decode_pair |>`
  \\ qexists_tac`mk_chu_morphism e2 (cf_external_mod b c) <| map_agent := I;
       map_env := encode_pair o pair$## I he o decode_pair |>`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`e2`, PULL_EXISTS, EXISTS_PROD, mk_cf_def]
    \\ simp[Once cf_external_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[Once cf_external_mod_def]
    \\ conj_tac >- metis_tac[BIJ_LINV_BIJ, INJ_DEF, BIJ_DEF]
    \\ simp[Abbr`d`, mk_cf_def, PULL_EXISTS]
    \\ simp[Once cf_external_def]
    \\ simp[Once cf_external_mod_def, PULL_EXISTS]
    \\ rpt gen_tac \\ strip_tac
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ drule BIJ_LINV_THM
    \\ simp[] \\ strip_tac
    \\ simp[Abbr`he`]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[Abbr`h`, mk_chu_morphism_def, restrict_def]
    \\ simp[cf_external_mod_def, cf_external_def, mk_cf_def])
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`e2`, PULL_EXISTS, EXISTS_PROD, mk_cf_def]
    \\ simp[Once cf_external_mod_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[Once cf_external_def]
    \\ conj_tac >- metis_tac[BIJ_LINV_BIJ, INJ_DEF, BIJ_DEF]
    \\ simp[Abbr`d`, mk_cf_def, PULL_EXISTS]
    \\ simp[Once cf_external_mod_def, PULL_EXISTS]
    \\ simp[Once cf_external_mod_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[Once cf_external_def]
    \\ rpt gen_tac \\ strip_tac
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ simp[Abbr`he`]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[Abbr`h`, mk_chu_morphism_def, restrict_def]
    \\ simp[cf_external_mod_def, cf_external_def, mk_cf_def])
  \\ simp[homotopic_id_map_agent_id]
  \\ imp_res_tac compose_in_chu
  \\ simp[mk_chu_morphism_def, restrict_def]
  \\ simp[Abbr`e2`]
QED

Theorem cf_external_multiplicative_subagent:
  c ∈ chu_objects w ∧ partitions b c.agent ⇒
  multiplicative_subagent (cf_external b c) c
Proof
  metis_tac[multiplicative_subagent_sister, is_sister_cf_external_mod]
QED

Theorem cf_external_mod_multiplicative_subagent:
  c ∈ chu_objects w ∧ partitions b c.agent ⇒
  multiplicative_subagent (cf_external_mod b c) c
Proof
  metis_tac[multiplicative_subagent_sister,
            is_sister_cf_external_mod, is_sister_comm]
QED

Definition cf_internal_def:
  cf_internal f c = mk_cf <| world := c.world;
    agent := IMAGE encode_pair (IMAGE encode_set f × c.agent);
    env := repfns f;
    eval := λp q. c.eval (SND (decode_pair p))
                         (decode_function q (FST (decode_pair p))) |>
End

Definition cf_internal_mod_def:
  cf_internal_mod f c = mk_cf <| world := c.world;
    agent := IMAGE encode_pair (repfns f × c.agent);
    env := IMAGE encode_set f;
    eval := λa e. c.eval (SND (decode_pair a))
                         (decode_function (FST (decode_pair a)) e) |>
End

Theorem swap_cf_internal:
  swap (cf_internal f c) = cf_external f (swap c)
Proof
  rw[cf_component_equality, cf_internal_def, cf_external_def]
  \\ rw[mk_cf_def, FUN_EQ_THM] \\ metis_tac[]
QED

Theorem swap_cf_internal_mod:
  swap (cf_internal_mod f c) = cf_external_mod f (swap c)
Proof
  rw[cf_component_equality, cf_internal_mod_def, cf_external_mod_def]
  \\ rw[mk_cf_def, FUN_EQ_THM] \\ metis_tac[]
QED

Theorem swap_cf_external:
  swap (cf_external f c) = cf_internal f (swap c)
Proof
  metis_tac[swap_cf_internal, swap_swap]
QED

Theorem swap_cf_external_mod:
  swap (cf_external_mod f c) = cf_internal_mod f (swap c)
Proof
  metis_tac[swap_cf_internal_mod, swap_swap]
QED

Theorem cf_internal_multiplicative_subagent:
  c ∈ chu_objects w ∧ partitions f c.env ⇒
  multiplicative_subagent c (cf_internal f c)
Proof
  rw[GSYM multiplicative_subenvironment_subagent]
  \\ rw[multiplicative_subenvironment_def]
  \\ rw[swap_cf_internal]
  \\ irule cf_external_multiplicative_subagent
  \\ rw[] \\ metis_tac[]
QED

Theorem cf_internal_mod_multiplicative_subagent:
  c ∈ chu_objects w ∧ partitions f c.env ⇒
  multiplicative_subagent c (cf_internal_mod f c)
Proof
  rw[GSYM multiplicative_subenvironment_subagent]
  \\ rw[multiplicative_subenvironment_def]
  \\ rw[swap_cf_internal_mod]
  \\ irule cf_external_mod_multiplicative_subagent
  \\ rw[] \\ metis_tac[]
QED

Definition commit_def:
  commit s c =
    cf_commit { a | a ∈ c.agent ∧ ∀e. e ∈ c.env ⇒ c.eval a e ∈ s } c
End

Definition commit_diff_def:
  commit_diff s c =
    cf_commit_diff { a | a ∈ c.agent ∧ ∀e. e ∈ c.env ⇒ c.eval a e ∈ s } c
End

Theorem is_brother_commit_diff:
  c ∈ chu_objects w ∧ s ⊆ w ⇒
  is_brother c (commit s c) (commit_diff s c)
Proof
  rw[commit_def, commit_diff_def]
  \\ irule is_brother_cf_commit_diff
  \\ rw[SUBSET_DEF]
  \\ metis_tac[]
QED

Theorem commit_additive_subagent:
  c ∈ chu_objects w ∧ s ⊆ w ⇒
  additive_subagent (commit s c) c
Proof
  metis_tac[is_brother_commit_diff, additive_subagent_brother]
QED

Theorem commit_diff_additive_subagent:
  c ∈ chu_objects w ∧ s ⊆ w ⇒
  additive_subagent (commit_diff s c) c
Proof
  metis_tac[is_brother_commit_diff, additive_subagent_brother, is_brother_comm]
QED

Theorem commit_in_chu_objects[simp]:
  c ∈ chu_objects w ⇒ commit s c ∈ chu_objects w
Proof
  rw[commit_def]
  \\ irule cf_commit_in_chu_objects
  \\ rw[SUBSET_DEF]
QED

Theorem commit_diff_in_chu_objects[simp]:
  c ∈ chu_objects w ⇒ commit_diff s c ∈ chu_objects w
Proof
  rw[commit_diff_def]
  \\ irule cf_commit_diff_in_chu_objects
  \\ rw[SUBSET_DEF]
QED

(* TODO: example of ¬(commit_diff s c ≅ commit (w DIFF s) c) *)

Definition assume_def:
  assume s c =
    cf_assume { e | e ∈ c.env ∧ ∀a. a ∈ c.agent ⇒ c.eval a e ∈ s } c
End

Definition assume_diff_def:
  assume_diff s c =
    cf_assume_diff { e | e ∈ c.env ∧ ∀a. a ∈ c.agent ⇒ c.eval a e ∈ s } c
End

Theorem swap_assume:
  swap (assume s c) = commit s (swap c)
Proof
  rw[assume_def, swap_cf_assume, commit_def]
QED

Theorem swap_assume_diff:
  swap (assume_diff s c) = commit_diff s (swap c)
Proof
  rw[assume_diff_def, swap_cf_assume_diff, commit_diff_def]
QED

Theorem swap_commit:
  swap (commit s c) = assume s (swap c)
Proof
  rw[commit_def, swap_cf_commit, assume_def]
QED

Theorem swap_commit_diff:
  swap (commit_diff s c) = assume_diff s (swap c)
Proof
  rw[commit_diff_def, swap_cf_commit_diff, assume_diff_def]
QED

Theorem assume_additive_subenvironment:
  c ∈ chu_objects w ∧ s ⊆ w ⇒
  additive_subenvironment c (assume s c)
Proof
  rw[assume_def]
  \\ irule cf_assume_additive_subenvironment
  \\ rw[SUBSET_DEF] \\ metis_tac[]
QED

Theorem assume_diff_additive_subenvironment:
  c ∈ chu_objects w ∧ s ⊆ w ⇒
  additive_subenvironment c (assume_diff s c)
Proof
  rw[assume_diff_def]
  \\ irule cf_assume_diff_additive_subenvironment
  \\ rw[SUBSET_DEF] \\ metis_tac[]
QED

Theorem assume_in_chu_objects[simp]:
  c ∈ chu_objects w ⇒ assume s c ∈ chu_objects w
Proof
  metis_tac[swap_assume, swap_swap, swap_in_chu_objects, commit_in_chu_objects]
QED

Theorem assume_diff_in_chu_objects[simp]:
  c ∈ chu_objects w ⇒ assume_diff s c ∈ chu_objects w
Proof
  metis_tac[swap_assume_diff, swap_swap,
            swap_in_chu_objects, commit_diff_in_chu_objects]
QED

Definition fn_partition_def:
  fn_partition s t f v =
    { { x' | x' ∈ s ∧
             ∀y. y ∈ t ⇒
                   (@w. w ∈ v ∧ f x y ∈ w) =
                   (@w. w ∈ v ∧ f x' y ∈ w) }
      | x | x ∈ s }
End

Theorem partitions_fn_partition:
  partitions v w ∧ (∀x y. x ∈ s ∧ y ∈ t ⇒ f x y ∈ w) ⇒
  partitions (fn_partition s t f v) s
Proof
  rw[partitions_thm, PULL_EXISTS]
  >- (
    fs[fn_partition_def]
    \\ simp[GSYM MEMBER_NOT_EMPTY]
    \\ metis_tac[])
  >- fs[fn_partition_def, SUBSET_DEF]
  \\ fs[EXISTS_UNIQUE_ALT]
  \\ simp[fn_partition_def]
  \\ qho_match_abbrev_tac`∃x. ∀x'. (∃x. x' = A x ∧ x ∈ s) ∧ y ∈ x' ⇔ x = x'`
  \\ qexists_tac`A y`
  \\ rw[EQ_IMP_THM]
  \\ gvs[Abbr`A`]
  \\ qexists_tac`y`
  \\ simp[]
QED

Definition external_def:
  external v c = cf_external (fn_partition c.agent c.env c.eval v) c
End

Definition external_mod_def:
  external_mod v c = cf_external_mod (fn_partition c.agent c.env c.eval v) c
End

Theorem is_sister_external_mod:
  c ∈ chu_objects w ∧ partitions v w ⇒
  is_sister c (external v c) (external_mod v c)
Proof
  rw[external_def, external_mod_def]
  \\ irule is_sister_cf_external_mod
  \\ conj_tac >- metis_tac[]
  \\ irule partitions_fn_partition
  \\ fs[in_chu_objects, wf_def]
  \\ metis_tac[]
QED

Theorem external_multiplicative_subagent:
  c ∈ chu_objects w ∧ partitions v w ⇒
  multiplicative_subagent (external v c) c
Proof
  metis_tac[is_sister_external_mod, multiplicative_subagent_sister]
QED

Theorem external_mod_multiplicative_subagent:
  c ∈ chu_objects w ∧ partitions v w ⇒
  multiplicative_subagent (external_mod v c) c
Proof
  metis_tac[is_sister_external_mod, multiplicative_subagent_sister, is_sister_comm]
QED

Theorem external_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ partitions v w ⇒ external v c ∈ chu_objects w
Proof
  rw[external_def]
  \\ irule cf_external_in_chu_objects
  \\ simp[]
  \\ irule partitions_fn_partition
  \\ fs[in_chu_objects, wf_def]
  \\ metis_tac[]
QED

Theorem external_mod_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ partitions v w ⇒ external_mod v c ∈ chu_objects w
Proof
  rw[external_mod_def]
  \\ irule cf_external_mod_in_chu_objects
  \\ simp[]
  \\ irule partitions_fn_partition
  \\ fs[in_chu_objects, wf_def]
  \\ metis_tac[]
QED

Definition internal_def:
  internal v c = cf_internal (fn_partition c.env c.agent (flip c.eval) v) c
End

Definition internal_mod_def:
  internal_mod v c = cf_internal_mod (fn_partition c.env c.agent (flip c.eval) v) c
End

Theorem swap_internal:
  swap (internal v c) = external v (swap c)
Proof
  rw[internal_def, external_def, swap_cf_internal]
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC) \\ simp[FUN_EQ_THM]
QED

Theorem swap_internal_mod:
  swap (internal_mod v c) = external_mod v (swap c)
Proof
  rw[internal_mod_def, external_mod_def, swap_cf_internal_mod]
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC) \\ simp[FUN_EQ_THM]
QED

Theorem swap_external:
  swap (external v c) = internal v (swap c)
Proof
  metis_tac[swap_swap, swap_internal]
QED

Theorem swap_external_mod:
  swap (external_mod v c) = internal_mod v (swap c)
Proof
  metis_tac[swap_swap, swap_internal_mod]
QED

Theorem internal_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ partitions v w ⇒ internal v c ∈ chu_objects w
Proof
  metis_tac[swap_internal, swap_swap, swap_in_chu_objects, external_in_chu_objects]
QED

Theorem internal_mod_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ partitions v w ⇒ internal_mod v c ∈ chu_objects w
Proof
  metis_tac[swap_internal_mod, swap_swap,
            swap_in_chu_objects, external_mod_in_chu_objects]
QED

Theorem internal_multiplicative_subagent:
  c ∈ chu_objects w ∧ partitions v w ⇒
  multiplicative_subagent c (internal v c)
Proof
  rw[GSYM multiplicative_subenvironment_subagent]
  \\ rw[multiplicative_subenvironment_def]
  \\ rw[swap_internal]
  \\ irule external_multiplicative_subagent
  \\ simp[] \\ metis_tac[]
QED

Theorem internal_mod_multiplicative_subagent:
  c ∈ chu_objects w ∧ partitions v w ⇒
  multiplicative_subagent c (internal_mod v c)
Proof
  rw[GSYM multiplicative_subenvironment_subagent]
  \\ rw[multiplicative_subenvironment_def]
  \\ rw[swap_internal_mod]
  \\ irule external_mod_multiplicative_subagent
  \\ simp[] \\ metis_tac[]
QED

Theorem homotopy_equiv_commit:
  c1 ≃ c2 -: w ∧ s ⊆ w ⇒
  commit s c1 ≃ commit s c2 -: w
Proof
  rw[homotopy_equiv_def]
  \\ qexists_tac`mk_chu_morphism (commit s c1) (commit s c2) f.map`
  \\ qexists_tac`mk_chu_morphism (commit s c2) (commit s c1) g.map`
  \\ conj_asm1_tac
  >- (
    fs[maps_to_in_chu]
    \\ fs[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ fs[SUBSET_DEF]
    \\ simp[commit_def, cf_commit_def]
    \\ simp[mk_cf_def]
    \\ metis_tac[] )
  \\ conj_asm1_tac
  >- (
    fs[maps_to_in_chu]
    \\ fs[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ fs[SUBSET_DEF]
    \\ simp[commit_def, cf_commit_def]
    \\ simp[mk_cf_def]
    \\ metis_tac[] )
  \\ `c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w` by metis_tac[maps_to_in_chu]
  \\ qmatch_goalsub_abbrev_tac`j o k -: _`
  \\ qpat_assum`f :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`g :- _ → _ -: _` o mp_then Any strip_assume_tac)
  \\ qpat_assum`g :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`f :- _ → _ -: _` o mp_then Any strip_assume_tac)
  \\ qpat_assum`j :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`k :- _ → _ -: _` o mp_then Any strip_assume_tac)
  \\ qpat_assum`k :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`j :- _ → _ -: _` o mp_then Any strip_assume_tac)
  \\ fs[homotopic_id_map_agent_id]
  \\ ntac 8 (pop_assum kall_tac)
  \\ qpat_x_assum`k :- _ → _ -: _`kall_tac
  \\ qpat_x_assum`j :- _ → _ -: _`kall_tac
  \\ gs[restrict_def, Abbr`j`, Abbr`k`, mk_chu_morphism_def, SUBSET_DEF]
  \\ fs[in_chu_objects, wf_def]
  \\ simp[commit_def, cf_commit_def, mk_cf_def, FUN_EQ_THM]
  \\ rw[] \\ rw[]
  \\ metis_tac[maps_to_in_chu, is_chu_morphism_def]
QED

Theorem homotopy_equiv_commit_diff:
  c1 ≃ c2 -: w ∧ s ⊆ w ⇒
  commit_diff s c1 ≃ commit_diff s c2 -: w
Proof
  rw[homotopy_equiv_def]
  \\ qexists_tac`mk_chu_morphism (commit_diff s c1) (commit_diff s c2) f.map`
  \\ qexists_tac`mk_chu_morphism (commit_diff s c2) (commit_diff s c1) g.map`
  \\ `c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w` by metis_tac[maps_to_in_chu]
  \\ qpat_assum`f :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`g :- _ → _ -: _` o mp_then Any strip_assume_tac)
  \\ qpat_assum`g :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`f :- _ → _ -: _` o mp_then Any strip_assume_tac)
  \\ qpat_assum`c1 ∈ _`(mp_then Any strip_assume_tac homotopic_id_map_agent_id)
  \\ qpat_assum`c2 ∈ _`(mp_then Any strip_assume_tac homotopic_id_map_agent_id)
  \\ qpat_assum`c1 ∈ _`(mp_then Any strip_assume_tac homotopic_id_map_env_id)
  \\ qpat_assum`c2 ∈ _`(mp_then Any strip_assume_tac homotopic_id_map_env_id)
  \\ fs[restrict_def]
  \\ ntac 4 (pop_assum mp_tac)
  \\ ntac 4 (pop_assum kall_tac)
  \\ ntac 4 strip_tac
  \\ conj_asm1_tac
  >- (
    fs[maps_to_in_chu]
    \\ fs[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ fs[SUBSET_DEF]
    \\ simp[commit_diff_def, cf_commit_diff_def]
    \\ simp[mk_cf_def]
    \\ metis_tac[] )
  \\ conj_asm1_tac
  >- (
    fs[maps_to_in_chu]
    \\ fs[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ fs[SUBSET_DEF]
    \\ simp[commit_diff_def, cf_commit_diff_def]
    \\ simp[mk_cf_def]
    \\ metis_tac[] )
  \\ qmatch_goalsub_abbrev_tac`j o k -: _`
  \\ qpat_assum`j :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`k :- _ → _ -: _` o mp_then Any strip_assume_tac)
  \\ qpat_assum`k :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`j :- _ → _ -: _` o mp_then Any strip_assume_tac)
  \\ `commit_diff s c1 ∈ chu_objects w ∧ commit_diff s c2 ∈ chu_objects w`
  by simp[]
  \\ qpat_assum`_ _ c1 ∈ _`(mp_then Any strip_assume_tac homotopic_id_map_agent_id)
  \\ qpat_assum`_ _ c2 ∈ _`(mp_then Any strip_assume_tac homotopic_id_map_agent_id)
  \\ qpat_assum`_ _ c1 ∈ _`(mp_then Any strip_assume_tac homotopic_id_map_env_id)
  \\ qpat_assum`_ _ c2 ∈ _`(mp_then Any strip_assume_tac homotopic_id_map_env_id)
  \\ simp[restrict_def]
  \\ ntac 6 (pop_assum mp_tac)
  \\ ntac 4 (pop_assum kall_tac)
  \\ ntac 6 strip_tac
  \\ qpat_x_assum`k :- _ → _ -: _`kall_tac
  \\ qpat_x_assum`j :- _ → _ -: _`kall_tac
  \\ gs[restrict_def, Abbr`j`, Abbr`k`, mk_chu_morphism_def, SUBSET_DEF]
  \\ fs[in_chu_objects, wf_def]
  \\ simp[commit_diff_def, cf_commit_diff_def, mk_cf_def, FUN_EQ_THM]
  \\ rw[] \\ rw[] \\ gs[]
  \\ metis_tac[maps_to_in_chu, is_chu_morphism_def]
QED

Theorem homotopy_equiv_assume:
  c1 ≃ c2 -: w ∧ s ⊆ w ⇒
  assume s c1 ≃ assume s c2 -: w
Proof
  strip_tac
  \\ `c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w`
  by metis_tac[homotopy_equiv_def, maps_to_in_chu]
  \\ DEP_ONCE_REWRITE_TAC[GSYM homotopy_equiv_swap]
  \\ simp_tac std_ss [swap_assume]
  \\ simp[]
  \\ irule homotopy_equiv_commit
  \\ simp[]
QED

Theorem homotopy_equiv_assume_diff:
  c1 ≃ c2 -: w ∧ s ⊆ w ⇒
  assume_diff s c1 ≃ assume_diff s c2 -: w
Proof
  strip_tac
  \\ `c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w`
  by metis_tac[homotopy_equiv_def, maps_to_in_chu]
  \\ DEP_ONCE_REWRITE_TAC[GSYM homotopy_equiv_swap]
  \\ simp_tac std_ss [swap_assume_diff]
  \\ simp[]
  \\ irule homotopy_equiv_commit_diff
  \\ simp[]
QED

val _ = export_theory();
