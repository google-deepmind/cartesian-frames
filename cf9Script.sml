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
  partitions X Y = ?R. R equiv_on Y /\ X = partition R Y
End

val _ = set_fixity "partitions" (Infix(NONASSOC, 425))

Theorem partitions_thm:
  X partitions Y <=>
  ((!x. x IN X ==> x <> {} /\ x SUBSET Y) /\
   (!y. y IN Y ==> ?!x. x IN X /\ y IN x))
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
  \\ qexists_tac`\y z. f y = f z`
  \\ simp[equiv_on_def]
  \\ conj_tac >- metis_tac[]
  \\ simp[partition_def, Once EXTENSION]
  \\ rw[EQ_IMP_THM]
  >- (
    `?a. a IN x /\ a IN Y` by metis_tac[MEMBER_NOT_EMPTY, SUBSET_DEF]
    \\ qexists_tac`a` \\ simp[]
    \\ `f a = x` by metis_tac[]
    \\ simp[EXTENSION]
    \\ metis_tac[SUBSET_DEF] )
  \\ `f y IN X /\ y IN f y` by metis_tac[]
  \\ qmatch_goalsub_abbrev_tac`z IN X`
  \\ `z = f y` suffices_by rw[]
  \\ rw[Abbr`z`, EXTENSION]
  \\ reverse(Cases_on`x IN Y`) \\ simp[]
  >- metis_tac[SUBSET_DEF]
  \\ metis_tac[]
QED

Theorem partitions_FINITE:
  X partitions Y ∧ FINITE Y ⇒
  FINITE X ∧ EVERY_FINITE X
Proof
  rw[partitions_def]
  \\ metis_tac[FINITE_partition]
QED

Theorem partitions_DISJOINT:
  v partitions w /\ s1 IN v /\ s2 IN v /\ s1 <> s2 ==>
  DISJOINT s1 s2
Proof
  rw[partitions_thm, IN_DISJOINT]
  \\ fs[EXISTS_UNIQUE_ALT, SUBSET_DEF]
  \\ metis_tac[]
QED

Definition is_repfn_def:
  is_repfn X q ⇔
  extensional q X ∧ ∀x. x ∈ X ⇒ q x ∈ x
End

Definition repfns_def:
  repfns b =
    { encode_function (IMAGE encode_set b)
        (restrict (q o decode_set) (IMAGE encode_set b))
      | q | is_repfn b q }
End

Theorem FINITE_is_repfn:
  FINITE b ∧ EVERY_FINITE b ⇒ FINITE { q | is_repfn b q}
Proof
  strip_tac
  \\ qspec_then`λq. IMAGE (λx. (x, q x)) b`irule FINITE_INJ
  \\ qexists_tac`b`
  \\ qmatch_goalsub_abbrev_tac`INJ f qs`
  \\ qexists_tac`IMAGE f qs`
  \\ conj_tac
  >- (
    irule SUBSET_FINITE
    \\ qexists_tac`POW (b × BIGUNION b)`
    \\ simp[SUBSET_DEF, PULL_EXISTS, Abbr`f`, Abbr`qs`]
    \\ simp[IN_POW, SUBSET_DEF, PULL_EXISTS]
    \\ simp[is_repfn_def]
    \\ metis_tac[] )
  \\ simp[INJ_DEF, PULL_EXISTS, Abbr`qs`]
  \\ rpt gen_tac \\ simp[is_repfn_def]
  \\ strip_tac
  \\ simp[Abbr`f`]
  \\ simp[Once EXTENSION, PULL_EXISTS]
  \\ strip_tac
  \\ simp[FUN_EQ_THM]
  \\ qx_gen_tac`z`
  \\ Cases_on`z ∈ b` \\ fs[extensional_def]
  \\ first_x_assum(qspec_then`(z, x z)`mp_tac)
  \\ simp[]
QED

Theorem FINITE_repfns[simp]:
  FINITE b ∧ EVERY_FINITE b ⇒ FINITE (repfns b)
Proof
  rw[repfns_def]
  \\ qho_match_abbrev_tac`FINITE {f q | is_repfn b q }`
  \\ qspec_then`λq. restrict (decode_function q o encode_set) b`
     irule FINITE_INJ
  \\ qexists_tac`b`
  \\ qexists_tac`{q | q | is_repfn b q}`
  \\ simp[FINITE_is_repfn]
  \\ simp[INJ_DEF, PULL_EXISTS]
  \\ `∀q. is_repfn b q ⇒ (restrict (decode_function (f q) o encode_set) b) = q`
  by (
    rw[is_repfn_def, Abbr`f`, FUN_EQ_THM, extensional_def]
    \\ Cases_on`x ∈ b` \\ rw[restrict_def]
    \\ metis_tac[])
  \\ simp[]
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

(* TODO: these could be used more *)

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
  c ∈ chu_objects w ∧ b partitions c.agent ⇒
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
  c ∈ chu_objects w ∧ b partitions c.agent ⇒
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
  c ∈ chu_objects w ∧ b partitions c.agent ⇒
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
  c ∈ chu_objects w ∧ b partitions c.agent ⇒
  multiplicative_subagent (cf_external b c) c
Proof
  metis_tac[multiplicative_subagent_sister, is_sister_cf_external_mod]
QED

Theorem cf_external_mod_multiplicative_subagent:
  c ∈ chu_objects w ∧ b partitions c.agent ⇒
  multiplicative_subagent (cf_external_mod b c) c
Proof
  metis_tac[multiplicative_subagent_sister,
            is_sister_cf_external_mod, is_sister_comm]
QED

Theorem image_cf_external:
  FINITE c.agent ∧ b partitions c.agent ⇒
  image (cf_external b c) = image c
Proof
  strip_tac
  \\ imp_res_tac partitions_FINITE
  \\ rw[image_def, cf_external_def, mk_cf_def, PULL_EXISTS, EXISTS_PROD,
        SET_EQ_SUBSET, SUBSET_DEF]
  >- (
    reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
    \\ fs[repfns_def]
    \\ simp[restrict_def]
    \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
    \\ fs[is_repfn_def]
    \\ fs[partitions_thm, SUBSET_DEF]
    \\ metis_tac[] )
  \\ qexists_tac`encode_repfn b (restrict (λs. if a ∈ s then a else CHOICE s) b)`
  \\ simp[encode_repfn_in_repfns]
  \\ qexistsl_tac[`e`,`@s. s ∈ b ∧ a ∈ s`]
  \\ SELECT_ELIM_TAC
  \\ conj_tac >- (fs[partitions_thm] \\ metis_tac[EXISTS_UNIQUE_ALT])
  \\ rpt gen_tac \\ strip_tac
  \\ simp[]
  \\ conj_asm1_tac
  >- (
    simp[is_repfn_def, restrict_def]
    \\ rw[]
    \\ fs[partitions_thm]
    \\ metis_tac[CHOICE_DEF])
  \\ reverse IF_CASES_TAC >- metis_tac[]
  \\ pop_assum kall_tac
  \\ simp[encode_repfn_def]
  \\ simp[restrict_def]
  \\ reverse IF_CASES_TAC >- metis_tac[]
  \\ rw[]
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
  c ∈ chu_objects w ∧ f partitions c.env ⇒
  multiplicative_subagent c (cf_internal f c)
Proof
  rw[GSYM multiplicative_subenvironment_subagent]
  \\ rw[multiplicative_subenvironment_def]
  \\ rw[swap_cf_internal]
  \\ irule cf_external_multiplicative_subagent
  \\ rw[] \\ metis_tac[]
QED

Theorem cf_internal_mod_multiplicative_subagent:
  c ∈ chu_objects w ∧ f partitions c.env ⇒
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

Theorem assume_null[simp]:
  assume s (null w) = null w
Proof
  rw[cf_component_equality, assume_def, cf_assume_def]
  \\ rw[mk_cf_def]
  \\ rw[FUN_EQ_THM]
QED

Theorem assume_empty_env:
  c ∈ chu_objects w ∧ c.env = ∅ ⇒
  assume s c = c
Proof
  rw[assume_def, cf_assume_def, mk_cf_def, cf_component_equality]
  \\ fs[in_chu_objects, wf_def]
  \\ rw[FUN_EQ_THM]
QED

Theorem assume_empty_agent:
  c ∈ chu_objects w ∧ c.agent = ∅ ⇒
  assume s c = c
Proof
  simp[assume_def, cf_assume_def]
  \\ rw[cf_component_equality]
  \\ simp[mk_cf_def, FUN_EQ_THM]
  \\ fs[in_chu_objects, wf_def]
QED

Theorem assume_empty:
  c ∈ chu_objects w ∧ c.agent ≠ ∅ ⇒
  assume ∅ c ≃ cfT w -: w
Proof
  rw[]
  \\ `assume ∅ c ∈ chu_objects w` by simp[]
  \\ fs[assume_def]
  \\ qmatch_goalsub_abbrev_tac`cf_assume b`
  \\ `b = ∅` by (
    simp[EXTENSION,Abbr`b`]
    \\ metis_tac[MEMBER_NOT_EMPTY] )
  \\ irule empty_env_nonempty_agent
  \\ simp[]
  \\ simp[cf_assume_def]
QED

Theorem image_assume_SUBSET:
  image (assume s c) ⊆ image c INTER s
Proof
  rw[image_def, assume_def, cf_assume_def, mk_cf_def, SUBSET_DEF]
  \\ rw[]
  \\ metis_tac[]
QED

Definition fn_part_def:
  fn_part s t f v x =
    { x' | x' ∈ s ∧
           ∀y. y ∈ t ⇒
                 (@w. w ∈ v ∧ f x y ∈ w) =
                 (@w. w ∈ v ∧ f x' y ∈ w) }
End

Definition fn_partition_def:
  fn_partition s t f v =
    { fn_part s t f v x | x | x ∈ s }
End

Theorem partitions_fn_partition:
  v partitions w ∧ (∀x y. x ∈ s ∧ y ∈ t ⇒ f x y ∈ w) ⇒
  (fn_partition s t f v) partitions s
Proof
  rw[partitions_thm, PULL_EXISTS]
  >- (
    fs[fn_partition_def]
    \\ simp[GSYM MEMBER_NOT_EMPTY, fn_part_def]
    \\ metis_tac[])
  >- fs[fn_partition_def, SUBSET_DEF, fn_part_def]
  \\ fs[EXISTS_UNIQUE_ALT]
  \\ simp[fn_partition_def]
  \\ qexists_tac`fn_part s t f v y`
  \\ rw[EQ_IMP_THM]
  \\ TRY(qexists_tac`y` \\ simp[])
  \\ gvs[fn_part_def]
QED

Theorem is_repfn_fn_partition:
  (is_repfn (fn_partition a e f v) q ⇔
   (extensional q (fn_partition a e f v)) ∧
   (IMAGE q (fn_partition a e f v) ⊆ a) ∧
   (∀x. x ∈ fn_partition a e f v ⇒ fn_part a e f v (q x) = x))
Proof
  rw[is_repfn_def]
  \\ Cases_on`extensional q (fn_partition a e f v)` \\ rw[]
  \\ eq_tac \\ strip_tac
  >- (
    simp[SUBSET_DEF, PULL_EXISTS]
    \\ rw[]
    \\ first_x_assum drule
    \\ fs[fn_partition_def]
    \\ qmatch_goalsub_abbrev_tac`qq ∈ _`
    \\ simp[Once fn_part_def]
    \\ strip_tac
    \\ simp[fn_part_def] )
  \\ rpt strip_tac
  \\ `q x ∈ fn_part a e f v (q x)` suffices_by metis_tac[]
  \\ simp_tac (srw_ss()) [fn_part_def]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
QED

Theorem FINITE_fn_partition:
  FINITE a ⇒
  FINITE (fn_partition a e f v) ∧
  EVERY_FINITE (fn_partition a e f v)
Proof
  rw[fn_partition_def]
  >- (
    qmatch_goalsub_abbrev_tac`FINITE s`
    \\ `s = IMAGE (fn_part a e f v) a`
    by ( rw[Abbr`s`, EXTENSION] )
    \\ rw[] )
  \\ rw[fn_part_def]
  \\ irule SUBSET_FINITE
  \\ qexists_tac`a`
  \\ simp[SUBSET_DEF]
QED

Theorem fn_part_image_subset_eq_agent:
  v partitions w ∧
  image c ⊆ s ∧ s ∈ v ∧ a ∈ c.agent
  ⇒
  fn_part c.agent c.env c.eval v a = c.agent
Proof
  rw[fn_part_def, Once SET_EQ_SUBSET, SUBSET_DEF]
  \\ fs[image_def, PULL_EXISTS]
  \\ fs[partitions_thm, EXISTS_UNIQUE_ALT]
  \\ fs[SUBSET_DEF]
  \\ metis_tac[]
QED

Definition external_def:
  external v c = cf_external (fn_partition c.agent c.env c.eval v) c
End

Definition external_mod_def:
  external_mod v c = cf_external_mod (fn_partition c.agent c.env c.eval v) c
End

Theorem is_sister_external_mod:
  c ∈ chu_objects w ∧ v partitions w ⇒
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
  c ∈ chu_objects w ∧ v partitions w ⇒
  multiplicative_subagent (external v c) c
Proof
  metis_tac[is_sister_external_mod, multiplicative_subagent_sister]
QED

Theorem external_mod_multiplicative_subagent:
  c ∈ chu_objects w ∧ v partitions w ⇒
  multiplicative_subagent (external_mod v c) c
Proof
  metis_tac[is_sister_external_mod, multiplicative_subagent_sister, is_sister_comm]
QED

Theorem external_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ v partitions w ⇒ external v c ∈ chu_objects w
Proof
  rw[external_def]
  \\ irule cf_external_in_chu_objects
  \\ simp[]
  \\ irule partitions_fn_partition
  \\ fs[in_chu_objects, wf_def]
  \\ metis_tac[]
QED

Theorem external_mod_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ v partitions w ⇒ external_mod v c ∈ chu_objects w
Proof
  rw[external_mod_def]
  \\ irule cf_external_mod_in_chu_objects
  \\ simp[]
  \\ irule partitions_fn_partition
  \\ fs[in_chu_objects, wf_def]
  \\ metis_tac[]
QED

Theorem image_external:
  c ∈ chu_objects w ∧ v partitions w ⇒
  image (external v c) = image c
Proof
  rw[external_def]
  \\ irule image_cf_external
  \\ metis_tac[partitions_fn_partition, in_chu_objects, wf_def, finite_cf_def]
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
  c ∈ chu_objects w ∧ v partitions w ⇒ internal v c ∈ chu_objects w
Proof
  metis_tac[swap_internal, swap_swap, swap_in_chu_objects, external_in_chu_objects]
QED

Theorem internal_mod_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ v partitions w ⇒ internal_mod v c ∈ chu_objects w
Proof
  metis_tac[swap_internal_mod, swap_swap,
            swap_in_chu_objects, external_mod_in_chu_objects]
QED

Theorem internal_multiplicative_subagent:
  c ∈ chu_objects w ∧ v partitions w ⇒
  multiplicative_subagent c (internal v c)
Proof
  rw[GSYM multiplicative_subenvironment_subagent]
  \\ rw[multiplicative_subenvironment_def]
  \\ rw[swap_internal]
  \\ irule external_multiplicative_subagent
  \\ simp[] \\ metis_tac[]
QED

Theorem internal_mod_multiplicative_subagent:
  c ∈ chu_objects w ∧ v partitions w ⇒
  multiplicative_subagent c (internal_mod v c)
Proof
  rw[GSYM multiplicative_subenvironment_subagent]
  \\ rw[multiplicative_subenvironment_def]
  \\ rw[swap_internal_mod]
  \\ irule external_mod_multiplicative_subagent
  \\ simp[] \\ metis_tac[]
QED

Theorem external_eval:
  (external v c).eval a e =
  if a ∈ (external v c).agent ∧ e ∈ (external v c).env then
    c.eval (decode_function a (FST (decode_pair e)))
      (SND (decode_pair e))
  else ARB
Proof
  rw[external_def, cf_external_def, mk_cf_def]
QED

Theorem internal_eval:
  (internal v c).eval a e =
  if a ∈ (internal v c).agent ∧ e ∈ (internal v c).env then
    c.eval (SND (decode_pair a))
      (decode_function e (FST (decode_pair a)))
  else ARB
Proof
  rw[internal_def, cf_internal_def, mk_cf_def]
QED

Theorem external_nonempty_agent:
  v partitions w ∧
  c ∈ chu_objects w ⇒
  (external v c).agent ≠ ∅
Proof
  strip_tac
  \\ `(fn_partition c.agent c.env c.eval v) partitions c.agent`
  by (
    irule partitions_fn_partition
    \\ metis_tac[in_chu_objects, wf_def] )
  \\ rw[external_def, cf_external_def]
  \\ fs[partitions_thm]
  \\ rw[repfns_def, GSYM MEMBER_NOT_EMPTY]
  \\ rw[is_repfn_def]
  \\ qmatch_goalsub_abbrev_tac`extensional _ fp`
  \\ qexists_tac`restrict CHOICE fp`
  \\ rw[]
  \\ rw[restrict_def]
  \\ irule CHOICE_DEF
  \\ metis_tac[]
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

Theorem homotopy_equiv_external_mod_both[local]:
  c1 ≃ c2 -: w ∧ v partitions w ⇒
  external v c1 ≃ external v c2 -: w ∧
  external_mod v c1 ≃ external_mod v c2 -: w
Proof
  simp[homotopy_equiv_def]
  \\ strip_tac
  \\ qabbrev_tac`b1 = fn_part c1.agent c1.env c1.eval v`
  \\ qabbrev_tac`b2 = fn_part c2.agent c2.env c2.eval v`
  \\ `SURJ b1 c1.agent (fn_partition c1.agent c1.env c1.eval v)`
  by ( simp[SURJ_DEF, fn_partition_def, PULL_EXISTS] \\ metis_tac[] )
  \\ drule SURJ_INJ_INV
  \\ disch_then(qx_choose_then`a1`strip_assume_tac)
  \\ `SURJ b2 c2.agent (fn_partition c2.agent c2.env c2.eval v)`
  by ( simp[SURJ_DEF, fn_partition_def, PULL_EXISTS] \\ metis_tac[] )
  \\ drule SURJ_INJ_INV
  \\ disch_then(qx_choose_then`a2`strip_assume_tac)
  \\ qabbrev_tac`i1 = b2 o f.map.map_agent o a1`
  \\ qabbrev_tac`i2 = b1 o g.map.map_agent o a2`
  \\ `c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w`
  by metis_tac[homotopy_equiv_def, maps_to_in_chu]
  \\ `restrict (b1 o g.map.map_agent o f.map.map_agent) c1.agent =
      restrict b1 c1.agent`
  by (
    simp[Abbr`b1`, FUN_EQ_THM, fn_part_def, restrict_def]
    \\ qpat_assum`f :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then(qpat_assum`g :- _ → _ -: _` o mp_then Any strip_assume_tac)
    \\ fs[homotopic_id_map_agent_id, restrict_def] )
  \\ `restrict (b2 o f.map.map_agent o g.map.map_agent) c2.agent =
      restrict b2 c2.agent`
  by (
    simp[Abbr`b2`, FUN_EQ_THM, fn_part_def, restrict_def]
    \\ qpat_assum`g :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then(qpat_assum`f :- _ → _ -: _` o mp_then Any strip_assume_tac)
    \\ fs[homotopic_id_map_agent_id, restrict_def] )
  \\ `restrict (i1 o b1) c1.agent =
      restrict (b2 o f.map.map_agent) c1.agent`
  by(
    simp[Abbr`i1`, restrict_def, FUN_EQ_THM]
    \\ qx_genl_tac[`a`,`b`]
    \\ IF_CASES_TAC \\ simp[]
    \\ qmatch_goalsub_abbrev_tac`b2 faba b`
    \\ reverse(Cases_on`b ∈ c2.agent`) >- simp[Abbr`b2`, fn_part_def]
    \\ `b1 a = b1 (a1 (b1 a))`
    by (
      irule EQ_SYM
      \\ first_x_assum irule
      \\ metis_tac[SURJ_DEF, maps_to_in_chu, is_chu_morphism_def] )
    \\ pop_assum mp_tac
    \\ simp[Abbr`b1`, Once fn_part_def]
    \\ qmatch_goalsub_abbrev_tac`a1 b1a`
    \\ simp[fn_part_def, EXTENSION]
    \\ disch_then(qspec_then`a`mp_tac) \\ simp[]
    \\ strip_tac
    \\ simp[Abbr`faba`]
    \\ simp[Abbr`b2`, fn_part_def]
    \\ AP_TERM_TAC \\ simp[Once FUN_EQ_THM]
    \\ qx_gen_tac`e` \\ Cases_on`e ∈ c2.env` \\ simp[]
    \\ fs[GSYM EXTENSION]
    \\ first_x_assum(qspec_then`f.map.map_env e`mp_tac)
    \\ impl_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ `c1.eval (a1 b1a) (f.map.map_env e) =
        c2.eval (f.map.map_agent (a1 b1a)) e`
    by PROVE_TAC[maps_to_in_chu, is_chu_morphism_def, INJ_DEF, SURJ_DEF]
    \\ pop_assum SUBST_ALL_TAC
    \\ disch_then SUBST_ALL_TAC
    \\ `c1.eval a (f.map.map_env e) =
        c2.eval (f.map.map_agent a) e`
    by PROVE_TAC[maps_to_in_chu, is_chu_morphism_def, INJ_DEF, SURJ_DEF]
    \\ pop_assum SUBST_ALL_TAC
    \\ metis_tac[] )
  \\ `restrict (i2 o b2) c2.agent =
      restrict (b1 o g.map.map_agent) c2.agent`
  by(
    simp[Abbr`i2`, restrict_def, FUN_EQ_THM]
    \\ qx_genl_tac[`a`,`b`]
    \\ IF_CASES_TAC \\ simp[]
    \\ qmatch_goalsub_abbrev_tac`b1 faba b`
    \\ reverse(Cases_on`b ∈ c1.agent`) >- simp[Abbr`b1`, fn_part_def]
    \\ `b2 a = b2 (a2 (b2 a))`
    by (
      irule EQ_SYM
      \\ first_x_assum irule
      \\ metis_tac[SURJ_DEF, maps_to_in_chu, is_chu_morphism_def] )
    \\ pop_assum mp_tac
    \\ simp[Abbr`b2`, Once fn_part_def]
    \\ qmatch_goalsub_abbrev_tac`a2 b2a`
    \\ simp[fn_part_def, EXTENSION]
    \\ disch_then(qspec_then`a`mp_tac) \\ simp[]
    \\ strip_tac
    \\ simp[Abbr`faba`]
    \\ simp[Abbr`b1`, fn_part_def]
    \\ AP_TERM_TAC \\ simp[Once FUN_EQ_THM]
    \\ qx_gen_tac`e` \\ Cases_on`e ∈ c1.env` \\ simp[]
    \\ fs[GSYM EXTENSION]
    \\ first_x_assum(qspec_then`g.map.map_env e`mp_tac)
    \\ impl_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ `c2.eval (a2 b2a) (g.map.map_env e) =
        c1.eval (g.map.map_agent (a2 b2a)) e`
    by PROVE_TAC[maps_to_in_chu, is_chu_morphism_def, INJ_DEF, SURJ_DEF]
    \\ pop_assum SUBST_ALL_TAC
    \\ disch_then SUBST_ALL_TAC
    \\ `c2.eval a (g.map.map_env e) =
        c1.eval (g.map.map_agent a) e`
    by PROVE_TAC[maps_to_in_chu, is_chu_morphism_def, INJ_DEF, SURJ_DEF]
    \\ pop_assum SUBST_ALL_TAC
    \\ metis_tac[] )
  \\ qmatch_assum_abbrev_tac`INJ a1 p1 _`
  \\ qmatch_assum_abbrev_tac`INJ a2 p2 _`
  \\ `restrict (i1 o i2) p2 = restrict (b2 o a2) p2`
  by (
    fs[Abbr`i1`, Abbr`i2`, restrict_def, Once FUN_EQ_THM]
    \\ gen_tac
    \\ IF_CASES_TAC \\ simp[]
    \\ metis_tac[INJ_DEF, maps_to_in_chu, is_chu_morphism_def] )
  \\ `restrict (i2 o i1) p1 = restrict (b1 o a1) p1`
  by (
    fs[Abbr`i1`, Abbr`i2`, restrict_def, Once FUN_EQ_THM]
    \\ gen_tac
    \\ IF_CASES_TAC \\ simp[]
    \\ metis_tac[INJ_DEF, maps_to_in_chu, is_chu_morphism_def] )
  \\ `∀q. is_repfn p1 q ⇒ is_repfn p2 (restrict (f.map.map_agent o q o i2) p2)`
  by (
    simp[Abbr`p1`, Abbr`p2`, is_repfn_fn_partition]
    \\ gen_tac
    \\ qmatch_goalsub_abbrev_tac`extensional q p1`
    \\ qmatch_goalsub_abbrev_tac`restrict _ p2`
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ simp[restrict_def]
    \\ strip_tac
    \\ `∀x. x ∈ p2 ⇒ i2 x ∈ p1`
    by (
      simp[Abbr`i2`]
      \\ metis_tac[SURJ_DEF, INJ_DEF, maps_to_in_chu, is_chu_morphism_def] )
    \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ fs[restrict_def] \\ metis_tac[])
  \\ `∀q. is_repfn p2 q ⇒ is_repfn p1 (restrict (g.map.map_agent o q o i1) p1)`
  by (
    simp[Abbr`p1`, Abbr`p2`, is_repfn_fn_partition]
    \\ gen_tac
    \\ qmatch_goalsub_abbrev_tac`extensional q p2`
    \\ qmatch_goalsub_abbrev_tac`restrict _ p1`
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ simp[restrict_def]
    \\ strip_tac
    \\ `∀x. x ∈ p1 ⇒ i1 x ∈ p2`
    by (
      simp[Abbr`i1`]
      \\ metis_tac[SURJ_DEF, INJ_DEF, maps_to_in_chu, is_chu_morphism_def] )
    \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ fs[restrict_def] \\ metis_tac[])
  \\ `FINITE p1 ∧ EVERY_FINITE p1`
  by (
    simp[Abbr`p1`]
    \\ irule FINITE_fn_partition
    \\ metis_tac[in_chu_objects, wf_def, finite_cf_def] )
  \\ `FINITE p2 ∧ EVERY_FINITE p2`
  by (
    simp[Abbr`p2`]
    \\ irule FINITE_fn_partition
    \\ metis_tac[in_chu_objects, wf_def, finite_cf_def] )
  \\ `(∀x. x ∈ p1 ⇒ i1 x ∈ p2) ∧ (∀x. x ∈ p2 ⇒ i2 x ∈ p1)`
  by (
    simp[Abbr`i2`, Abbr`i1`]
    \\ metis_tac[INJ_DEF, SURJ_DEF, maps_to_in_chu, is_chu_morphism_def] )
  \\ conj_tac
  >- (
    qexists_tac`mk_chu_morphism (external v c1) (external v c2) <|
         map_agent := λq.
           encode_function (IMAGE encode_set p2)
             (restrict (f.map.map_agent o (decode_function q o encode_set) o i2 o decode_set) (IMAGE encode_set p2));
         map_env := λe. encode_pair
           (encode_set (i2 (decode_set (FST (decode_pair e)))),
            f.map.map_env (SND (decode_pair e))) |>`
    \\ qmatch_goalsub_abbrev_tac`_ o k -: _`
    \\ qexists_tac`mk_chu_morphism (external v c2) (external v c1) <|
         map_agent := λq.
           encode_function (IMAGE encode_set p1)
             (restrict (g.map.map_agent o (decode_function q o encode_set) o i1 o decode_set) (IMAGE encode_set p1));
         map_env := λe. encode_pair
           (encode_set (i1 (decode_set (FST (decode_pair e)))),
            g.map.map_env (SND (decode_pair e))) |>`
    \\ qmatch_goalsub_abbrev_tac`j o k -: _`
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu, Abbr`k`]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[external_def]
      \\ simp[Once cf_external_def, PULL_EXISTS, EXISTS_PROD]
      \\ simp[Once cf_external_def, PULL_EXISTS, EXISTS_PROD]
      \\ conj_asm1_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
      \\ simp[Once cf_external_def, PULL_EXISTS, EXISTS_PROD]
      \\ simp[repfns_def, PULL_EXISTS]
      \\ simp[Once cf_external_def, PULL_EXISTS, EXISTS_PROD]
      \\ simp[repfns_def, PULL_EXISTS]
      \\ qho_match_abbrev_tac`(∀q. is_repfn p1 q ⇒ ∃q'. P q q') ∧ _`
      \\ `∀q. is_repfn p1 q ⇒ P q (restrict (f.map.map_agent o q o i2) p2)`
      by (
        rpt strip_tac
        \\ simp[Abbr`P`]
        \\ AP_TERM_TAC
        \\ simp[FUN_EQ_THM, restrict_def]
        \\ gen_tac
        \\ IF_CASES_TAC \\ simp[]
        \\ pop_assum strip_assume_tac
        \\ simp[]
        \\ IF_CASES_TAC \\ simp[]
        \\ metis_tac[] )
      \\ conj_tac >- metis_tac[]
      \\ simp[Once cf_external_def, PULL_EXISTS, EXISTS_PROD]
      \\ simp[Once cf_external_def, PULL_EXISTS, EXISTS_PROD]
      \\ simp[repfns_def, PULL_EXISTS]
      \\ simp[cf_external_def, mk_cf_def]
      \\ rpt gen_tac \\ strip_tac
      \\ simp[repfns_def, PULL_EXISTS]
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ pop_assum kall_tac
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ pop_assum kall_tac
      \\ first_x_assum drule
      \\ simp[Abbr`P`] \\ strip_tac
      \\ qunabbrev_tac`j`
      \\ simp[restrict_def]
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ `q (i2 x) ∈ c1.agent` suffices_by
      metis_tac[maps_to_in_chu, is_chu_morphism_def]
      \\ `q (i2 x) ∈ i2 x` by metis_tac[is_repfn_def]
      \\ `i2 x ∈ p1` by metis_tac[]
      \\ ntac 2 (pop_assum mp_tac)
      \\ simp_tac(srw_ss())[Abbr`p1`, fn_partition_def, PULL_EXISTS]
      \\ rpt strip_tac \\ fs[fn_part_def] )
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu, Abbr`j`]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[external_def]
      \\ simp[Once cf_external_def, PULL_EXISTS, EXISTS_PROD]
      \\ simp[Once cf_external_def, PULL_EXISTS, EXISTS_PROD]
      \\ conj_asm1_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
      \\ simp[Once cf_external_def, PULL_EXISTS, EXISTS_PROD]
      \\ simp[repfns_def, PULL_EXISTS]
      \\ simp[Once cf_external_def, PULL_EXISTS, EXISTS_PROD]
      \\ simp[repfns_def, PULL_EXISTS]
      \\ qho_match_abbrev_tac`(∀q. is_repfn p2 q ⇒ ∃q'. P q q') ∧ _`
      \\ `∀q. is_repfn p2 q ⇒ P q (restrict (g.map.map_agent o q o i1) p1)`
      by (
        rpt strip_tac
        \\ simp[Abbr`P`]
        \\ AP_TERM_TAC
        \\ simp[FUN_EQ_THM, restrict_def]
        \\ gen_tac
        \\ IF_CASES_TAC \\ simp[]
        \\ pop_assum strip_assume_tac
        \\ simp[]
        \\ IF_CASES_TAC \\ simp[]
        \\ metis_tac[] )
      \\ conj_tac >- metis_tac[]
      \\ simp[Once cf_external_def, PULL_EXISTS, EXISTS_PROD]
      \\ simp[Once cf_external_def, PULL_EXISTS, EXISTS_PROD]
      \\ simp[repfns_def, PULL_EXISTS]
      \\ simp[cf_external_def, mk_cf_def]
      \\ rpt gen_tac \\ strip_tac
      \\ simp[repfns_def, PULL_EXISTS]
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ pop_assum kall_tac
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ pop_assum kall_tac
      \\ first_x_assum drule
      \\ simp[Abbr`P`] \\ strip_tac
      \\ qunabbrev_tac`k`
      \\ simp[restrict_def]
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ `q (i1 x) ∈ c2.agent` suffices_by
      metis_tac[maps_to_in_chu, is_chu_morphism_def]
      \\ `q (i1 x) ∈ i1 x` by metis_tac[is_repfn_def]
      \\ `i1 x ∈ p2` by metis_tac[]
      \\ ntac 2 (pop_assum mp_tac)
      \\ simp_tac(srw_ss())[Abbr`p2`, fn_partition_def, PULL_EXISTS]
      \\ rpt strip_tac \\ fs[fn_part_def] )
    \\ qpat_assum`k :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then(qpat_assum`j :- _ → _ -: _` o mp_then Any strip_assume_tac)
    \\ qpat_assum`j :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then(qpat_assum`k :- _ → _ -: _` o mp_then Any strip_assume_tac)
    \\ simp[homotopic_id_map_env_id]
    \\ simp[restrict_def]
    \\ ntac 6 (pop_assum kall_tac)
    \\ simp[Abbr`j`, Abbr`k`, mk_chu_morphism_def, restrict_def]
    \\ simp[external_def]
    \\ simp[Once cf_external_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[Once CONJ_COMM]
    \\ simp[Once cf_external_def, PULL_EXISTS, EXISTS_PROD]
    \\ conj_tac
    >- (
      rpt gen_tac \\ strip_tac
      \\ reverse IF_CASES_TAC
      >- (
        `F` suffices_by rw[]
        \\ pop_assum mp_tac
        \\ simp[cf_external_def]
        \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
      \\ `i1 (i2 x) = x` by (fs[restrict_def] \\ metis_tac[])
      \\ simp[]
      \\ simp[cf_external_def, mk_cf_def]
      \\ irule EQ_SYM
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
      \\ qpat_assum`g :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
      \\ disch_then(qpat_assum`f :- _ → _ -: _` o mp_then Any strip_assume_tac)
      \\ fs[homotopic_id_map_env_id, restrict_def] )
    \\ rpt gen_tac \\ strip_tac
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[cf_external_def]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ `i2 (i1 x) = x` by (fs[restrict_def] \\ metis_tac[])
    \\ simp[]
    \\ simp[cf_external_def, mk_cf_def]
    \\ irule EQ_SYM
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ qpat_assum`f :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then(qpat_assum`g :- _ → _ -: _` o mp_then Any strip_assume_tac)
    \\ fs[homotopic_id_map_env_id, restrict_def])
  \\ qexists_tac`mk_chu_morphism (external_mod v c1) (external_mod v c2) <|
       map_agent := encode_set o i1 o decode_set;
       map_env := λe. encode_pair
         (encode_function (IMAGE encode_set p1) (restrict (g.map.map_agent o (decode_function (FST (decode_pair e)) o encode_set) o i1 o decode_set) (IMAGE encode_set p1)),
          f.map.map_env (SND (decode_pair e))) |>`
  \\ qmatch_goalsub_abbrev_tac`_ o k -: _`
  \\ qexists_tac`mk_chu_morphism (external_mod v c2) (external_mod v c1) <|
       map_agent := encode_set o i2 o decode_set;
       map_env := λe. encode_pair
         (encode_function (IMAGE encode_set p2) (restrict (f.map.map_agent o (decode_function (FST (decode_pair e)) o encode_set) o i2 o decode_set) (IMAGE encode_set p2)),
          g.map.map_env (SND (decode_pair e))) |>`
  \\ qmatch_goalsub_abbrev_tac`j o k -: _`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu, Abbr`k`]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[external_mod_def]
    \\ simp[Once cf_external_mod_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[repfns_def, PULL_EXISTS]
    \\ simp[Once cf_external_mod_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[repfns_def, PULL_EXISTS]
    \\ qho_match_abbrev_tac`(∀e q. is_repfn p2 q ∧ e ∈ c2.env ⇒
          ∃q'. P q q' ∧ f.map.map_env e ∈ c1.env ) ∧ _ ∧ _`
    \\ `∀q. is_repfn p2 q ⇒ P q (restrict (g.map.map_agent o q o i1) p1)`
    by (
      rpt strip_tac
      \\ simp[Abbr`P`]
      \\ AP_TERM_TAC
      \\ simp[FUN_EQ_THM, restrict_def]
      \\ gen_tac
      \\ IF_CASES_TAC \\ simp[]
      \\ pop_assum strip_assume_tac
      \\ simp[]
      \\ IF_CASES_TAC \\ simp[]
      \\ metis_tac[] )
    \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ simp[Once cf_external_mod_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[Once cf_external_mod_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[Once cf_external_mod_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[Once cf_external_mod_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[repfns_def, PULL_EXISTS]
    \\ simp[cf_external_mod_def, mk_cf_def]
    \\ rpt gen_tac \\ strip_tac
    \\ simp[repfns_def, PULL_EXISTS]
    \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ pop_assum kall_tac
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum kall_tac
    \\ first_x_assum drule
    \\ simp[Abbr`P`]
    \\ disch_then kall_tac
    \\ qunabbrev_tac`j`
    \\ simp[restrict_def]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ qpat_assum`g :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then(qpat_assum`f :- _ → _ -: _` o mp_then Any strip_assume_tac)
    \\ fs[homotopic_id_map_agent_id, restrict_def]
    \\ `q (i1 x) ∈ c2.agent` suffices_by
    metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ `q (i1 x) ∈ i1 x` by metis_tac[is_repfn_def]
    \\ `i1 x ∈ p2` by metis_tac[]
    \\ ntac 2 (pop_assum mp_tac)
    \\ simp_tac(srw_ss())[Abbr`p2`, fn_partition_def, PULL_EXISTS]
    \\ rpt strip_tac \\ fs[fn_part_def] )
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu, Abbr`j`]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[external_mod_def]
    \\ simp[Once cf_external_mod_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[repfns_def, PULL_EXISTS]
    \\ simp[Once cf_external_mod_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[repfns_def, PULL_EXISTS]
    \\ qho_match_abbrev_tac`(∀e q. is_repfn p1 q ∧ e ∈ c1.env ⇒
          ∃q'. P q q' ∧ g.map.map_env e ∈ c2.env ) ∧ _ ∧ _`
    \\ `∀q. is_repfn p1 q ⇒ P q (restrict (f.map.map_agent o q o i2) p2)`
    by (
      rpt strip_tac
      \\ simp[Abbr`P`]
      \\ AP_TERM_TAC
      \\ simp[FUN_EQ_THM, restrict_def]
      \\ gen_tac
      \\ IF_CASES_TAC \\ simp[]
      \\ pop_assum strip_assume_tac
      \\ simp[]
      \\ IF_CASES_TAC \\ simp[]
      \\ metis_tac[] )
    \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ simp[Once cf_external_mod_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[Once cf_external_mod_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[Once cf_external_mod_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[Once cf_external_mod_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[repfns_def, PULL_EXISTS]
    \\ simp[cf_external_mod_def, mk_cf_def]
    \\ rpt gen_tac \\ strip_tac
    \\ simp[repfns_def, PULL_EXISTS]
    \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ pop_assum kall_tac
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum kall_tac
    \\ first_x_assum drule
    \\ simp[Abbr`P`]
    \\ disch_then kall_tac
    \\ qunabbrev_tac`k`
    \\ simp[restrict_def]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ qpat_assum`f :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then(qpat_assum`g :- _ → _ -: _` o mp_then Any strip_assume_tac)
    \\ fs[homotopic_id_map_agent_id, restrict_def]
    \\ `q (i2 x) ∈ c1.agent` suffices_by
    metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ `q (i2 x) ∈ i2 x` by metis_tac[is_repfn_def]
    \\ `i2 x ∈ p1` by metis_tac[]
    \\ ntac 2 (pop_assum mp_tac)
    \\ simp_tac(srw_ss())[Abbr`p1`, fn_partition_def, PULL_EXISTS]
    \\ rpt strip_tac \\ fs[fn_part_def] )
  \\ qpat_assum`k :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`j :- _ → _ -: _` o mp_then Any strip_assume_tac)
  \\ qpat_assum`j :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`k :- _ → _ -: _` o mp_then Any strip_assume_tac)
  \\ simp[homotopic_id_map_agent_id]
  \\ simp[restrict_def]
  \\ ntac 6 (pop_assum kall_tac)
  \\ simp[Abbr`j`, Abbr`k`, mk_chu_morphism_def, restrict_def]
  \\ simp[external_mod_def]
  \\ simp[Once cf_external_mod_def, PULL_EXISTS, EXISTS_PROD]
  \\ simp[Once CONJ_COMM]
  \\ simp[Once cf_external_mod_def, PULL_EXISTS, EXISTS_PROD]
  \\ conj_tac
  >- (
    rpt gen_tac \\ strip_tac
    \\ reverse IF_CASES_TAC
    >- ( `F` suffices_by rw[] \\ pop_assum mp_tac \\ simp[cf_external_mod_def])
    \\ `i1 (i2 x) = x` by (fs[restrict_def] \\ metis_tac[])
    \\ simp[])
  \\ rpt gen_tac \\ strip_tac
  \\ reverse IF_CASES_TAC
  >- ( `F` suffices_by rw[] \\ pop_assum mp_tac \\ simp[cf_external_mod_def])
  \\ `i2 (i1 x) = x` by (fs[restrict_def] \\ metis_tac[])
  \\ simp[]
QED

Theorem homotopy_equiv_external:
  c1 ≃ c2 -: w ∧ v partitions w ⇒
  external v c1 ≃ external v c2 -: w
Proof
  metis_tac[homotopy_equiv_external_mod_both]
QED

Theorem homotopy_equiv_external_mod:
  c1 ≃ c2 -: w ∧ v partitions w ⇒
  external_mod v c1 ≃ external_mod v c2 -: w
Proof
  metis_tac[homotopy_equiv_external_mod_both]
QED

Theorem homotopy_equiv_internal:
  c1 ≃ c2 -: w ∧ v partitions w ⇒
  internal v c1 ≃ internal v c2 -: w
Proof
  strip_tac
  \\ `c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w` by metis_tac[homotopy_equiv_def, maps_to_in_chu]
  \\ DEP_ONCE_REWRITE_TAC[GSYM homotopy_equiv_swap]
  \\ simp[swap_internal, Excl"homotopy_equiv_swap"]
  \\ irule homotopy_equiv_external
  \\ simp[]
QED

Theorem homotopy_equiv_internal_mod:
  c1 ≃ c2 -: w ∧ v partitions w ⇒
  internal_mod v c1 ≃ internal_mod v c2 -: w
Proof
  strip_tac
  \\ `c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w` by metis_tac[homotopy_equiv_def, maps_to_in_chu]
  \\ DEP_ONCE_REWRITE_TAC[GSYM homotopy_equiv_swap]
  \\ simp[swap_internal_mod, Excl"homotopy_equiv_swap"]
  \\ irule homotopy_equiv_external_mod
  \\ simp[]
QED

Theorem commit_lollipop_cf1:
  c ∈ chu_objects w ∧ s ⊆ w ⇒
  commit s c ≅ lollipop (cf1 w s) c -: chu w
Proof
  strip_tac
  \\ simp[Once iso_objs_sym]
  \\ rw[iso_objs_thm]
  \\ imp_res_tac in_chu_objects_finite_world
  \\ qexists_tac`mk_chu_morphism (lollipop (cf1 w s) c) (commit s c)
       <| map_agent := λm. (decode_morphism (cf1 w s) c m).map.map_agent "";
          map_env := λe. encode_pair ("", e) |>`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[lollipop_def, commit_def, cf_commit_def, hom_def,
            PULL_EXISTS, mk_cf_def]
    \\ conj_asm1_tac
    >- (
      gen_tac \\ strip_tac
      \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
      \\ fs[maps_to_in_chu, is_chu_morphism_def]
      \\ rfs[cf1_def, mk_cf_def] \\ metis_tac[] )
    \\ rpt gen_tac \\ strip_tac
    \\ simp[]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ simp[]
    \\ fs[maps_to_in_chu, is_chu_morphism_def] )
  \\ simp[chu_iso_bij, CONJ_ASSOC]
  \\ fs[maps_to_in_chu, is_chu_morphism_def]
  \\ gs[mk_chu_morphism_def, restrict_def]
  \\ reverse conj_tac
  >- (
    simp[BIJ_IFF_INV, PULL_EXISTS]
    \\ gs[lollipop_def, commit_def, cf_commit_def, mk_cf_def,
          PULL_EXISTS, EXISTS_PROD]
    \\ qexists_tac`SND o decode_pair` \\ simp[] )
  \\ simp[BIJ_DEF]
  \\ simp[INJ_DEF]
  \\ simp[Once lollipop_def, PULL_EXISTS]
  \\ simp[Once lollipop_def, PULL_EXISTS]
  \\ conj_tac
  >- (
    rpt gen_tac
    \\ simp[hom_def]
    \\ strip_tac
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[] \\ strip_tac
    \\ AP_TERM_TAC
    \\ simp[morphism_component_equality]
    \\ fs[maps_to_in_chu]
    \\ simp[chu_morphism_map_component_equality, FUN_EQ_THM]
    \\ fs[is_chu_morphism_def]
    \\ fs[extensional_def]
    \\ conj_tac >- metis_tac[]
    \\ qx_gen_tac`e`
    \\ reverse(Cases_on`e ∈ c.env`) >- metis_tac[]
    \\ gs[cf1_def, mk_cf_def] )
  \\ simp[SURJ_DEF]
  \\ gs[commit_def, cf_commit_def, mk_cf_def, PULL_EXISTS]
  \\ rpt strip_tac
  \\ simp[lollipop_def, PULL_EXISTS, hom_def]
  \\ qexists_tac`mk_chu_morphism (cf1 w s) c <| map_agent := K x; map_env := λb. c.eval x b |>`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[cf1_def, mk_cf_def] )
  \\ reverse IF_CASES_TAC >- metis_tac[]
  \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
  \\ simp[]
  \\ simp[mk_chu_morphism_def]
  \\ rw[restrict_def]
QED

Theorem assume_tensor_cf1:
  c ∈ chu_objects w ∧ s ⊆ w ⇒
  assume s c ≅ tensor (cf1 w s) c -: chu w
Proof
  strip_tac
  \\ imp_res_tac in_chu_objects_finite_world
  \\ irule iso_objs_trans \\ simp[]
  \\ qexists_tac`swap (commit s (swap c))`
  \\ simp[Once swap_commit]
  \\ irule iso_objs_trans \\ simp[]
  \\ qexists_tac`swap (lollipop (cf1 w s) (swap c))`
  \\ conj_tac >- simp[commit_lollipop_cf1]
  \\ simp[lollipop_eq_par]
  \\ simp[GSYM swap_tensor_par]
QED

Theorem commit_subagent_cfbot:
  c ∈ chu_objects w ∧ s ⊆ w ⇒
  commit s c ◁ cfbot w s -: w
Proof
  simp[subagent_cfbot_image]
  \\ simp[image_def, commit_def, cf_commit_def,
          PULL_EXISTS, SUBSET_DEF, mk_cf_def]
QED

Theorem assume_subagent_cfbot:
  c ∈ chu_objects w ∧ s ⊆ w ⇒
  assume s c ◁ cfbot w s -: w
Proof
  simp[subagent_cfbot_image]
  \\ simp[image_def, assume_def, cf_assume_def,
          PULL_EXISTS, SUBSET_DEF, mk_cf_def]
QED

Theorem subagent_cfbot_commit_assume_eq:
  s ⊆ w ∧ c ◁ cfbot w s -: w ⇒
  commit s c = c ∧ assume s c = c
Proof
  strip_tac
  \\ `c ∈ chu_objects w ∧ FINITE w`
  by metis_tac[subagent_def, in_chu_objects_finite_world]
  \\ gs[subagent_cfbot_image]
  \\ simp[commit_def, cf_commit_def, assume_def, cf_assume_def]
  \\ qmatch_goalsub_abbrev_tac`c with agent := a`
  \\ qmatch_goalsub_abbrev_tac`c with env := e`
  \\ `a = c.agent` by (
    simp[SET_EQ_SUBSET, SUBSET_DEF, Abbr`a`]
    \\ fs[image_def, PULL_EXISTS, SUBSET_DEF] )
  \\ `e = c.env` by (
    simp[SET_EQ_SUBSET, SUBSET_DEF, Abbr`e`]
    \\ fs[image_def, PULL_EXISTS, SUBSET_DEF] )
  \\ simp[cf_component_equality, mk_cf_def, FUN_EQ_THM]
  \\ metis_tac[in_chu_objects, wf_def]
QED

Theorem commit_idem:
  s ⊆ w ∧ c ∈ chu_objects w ⇒
  commit s (commit s c) = commit s c
Proof
  metis_tac[subagent_cfbot_commit_assume_eq, commit_subagent_cfbot]
QED

Theorem assume_idem:
  s ⊆ w ∧ c ∈ chu_objects w ⇒
  assume s (assume s c) = assume s c
Proof
  metis_tac[subagent_cfbot_commit_assume_eq, assume_subagent_cfbot]
QED

Theorem commit_diff_exists_not_in:
  ∀a. a ∈ (commit_diff s c).agent ⇒
      ∃e. e ∈ (commit_diff s c).env ∧
          (commit_diff s c).eval a e ∉ s
Proof
  rw[commit_diff_def, cf_commit_diff_def, PULL_EXISTS, mk_cf_def]
  \\ qexists_tac`e` \\ rw[]
QED

Theorem exists_not_in_commit_diff_eq:
  wf c ∧
  (∀a. a ∈ c.agent ⇒ ∃e. e ∈ c.env ∧ c.eval a e ∉ s) ⇒
  commit_diff s c = c
Proof
  rw[commit_diff_def, cf_commit_diff_def]
  \\ qmatch_goalsub_abbrev_tac`c with agent := b`
  \\ `b = c.agent`
  by ( simp[Abbr`b`, SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS] )
  \\ simp[cf_component_equality, mk_cf_def, FUN_EQ_THM]
  \\ metis_tac[wf_def]
QED

Theorem commit_diff_idem:
  c ∈ chu_objects w ⇒
  commit_diff s (commit_diff s c) = commit_diff s c
Proof
  metis_tac[in_chu_objects, exists_not_in_commit_diff_eq,
            commit_diff_exists_not_in, commit_diff_in_chu_objects]
QED

Theorem assume_diff_exists_not_in:
  ∀e. e ∈ (assume_diff s c).env ⇒
      ∃a. a ∈ (assume_diff s c).agent ∧
          (assume_diff s c).eval a e ∉ s
Proof
  rw[assume_diff_def, cf_assume_diff_def, PULL_EXISTS, mk_cf_def]
  \\ qexists_tac`a` \\ rw[]
QED

Theorem exists_not_in_assume_diff_eq:
  wf c ∧
  (∀e. e ∈ c.env ⇒ ∃a. a ∈ c.agent ∧ c.eval a e ∉ s) ⇒
  assume_diff s c = c
Proof
  rw[assume_diff_def, cf_assume_diff_def]
  \\ qmatch_goalsub_abbrev_tac`c with env := b`
  \\ `b = c.env`
  by ( simp[Abbr`b`, SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS] )
  \\ simp[cf_component_equality, mk_cf_def, FUN_EQ_THM]
  \\ metis_tac[wf_def]
QED

Theorem assume_diff_idem:
  c ∈ chu_objects w ⇒
  assume_diff s (assume_diff s c) = assume_diff s c
Proof
  metis_tac[in_chu_objects, exists_not_in_assume_diff_eq,
            assume_diff_exists_not_in, assume_diff_in_chu_objects]
QED

Theorem external_equal_parts:
  c ∈ chu_objects w ∧ v partitions w ⇒
  (external v c).agent ≠ ∅ ∧
  (∀a1 a2 e.
    a1 ∈ (external v c).agent ∧
    a2 ∈ (external v c).agent ∧
    e ∈ (external v c).env
    ⇒
    (@w. w ∈ v ∧ ((external v c).eval a1 e) ∈ w) =
    (@w. w ∈ v ∧ ((external v c).eval a2 e) ∈ w))
Proof
  rw[external_def, cf_external_def, EXISTS_PROD]
  >- (
    rw[repfns_def, GSYM MEMBER_NOT_EMPTY]
    \\ rw[is_repfn_fn_partition]
    \\ rw[fn_partition_def, PULL_EXISTS]
    \\ qmatch_goalsub_abbrev_tac`extensional _ s`
    \\ qexists_tac`restrict (λp. @x. x ∈ c.agent ∧ p = fn_part c.agent c.env c.eval v x) s`
    \\ simp[]
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ simp[restrict_def]
    \\ simp[Abbr`s`, PULL_EXISTS]
    \\ metis_tac[] )
  \\ simp[mk_cf_def]
  \\ IF_CASES_TAC \\ simp[]
  \\ pop_assum kall_tac
  \\ qmatch_assum_rename_tac`e ∈ c.env`
  \\ fs[repfns_def]
  \\ DEP_REWRITE_TAC[decode_encode_function]
  \\ `FINITE c.agent` by metis_tac[in_chu_objects, wf_def, finite_cf_def]
  \\ simp[FINITE_fn_partition]
  \\ simp[restrict_def]
  \\ imp_res_tac FINITE_fn_partition
  \\ fs[is_repfn_def]
  \\ IF_CASES_TAC \\ simp[]
  \\ pop_assum kall_tac
  \\ qpat_x_assum`a1 = _`kall_tac
  \\ qpat_x_assum`a2 = _`kall_tac
  \\ fs[partitions_thm, EXISTS_UNIQUE_ALT]
  \\ `q x ∈ x ∧ q' x ∈ x` by metis_tac[]
  \\ `∃a. a ∈ c.agent ∧ x = fn_part c.agent c.env c.eval v a`
  by (fs[fn_partition_def] \\ metis_tac[])
  \\ qmatch_assum_abbrev_tac`q2 ∈ x`
  \\ qpat_x_assum`q2 ∈ _`mp_tac
  \\ qmatch_assum_abbrev_tac`q1 ∈ x`
  \\ strip_tac
  \\ BasicProvers.VAR_EQ_TAC
  \\ fs[fn_part_def]
QED

Theorem equal_parts_external_iso:
  c ∈ chu_objects w ∧ v partitions w ∧
  c.agent ≠ ∅ ∧
  (∀a1 a2 e.
    a1 ∈ c.agent ∧ a2 ∈ c.agent ∧ e ∈ c.env ⇒
    (@w. w ∈ v ∧ (c.eval a1 e) ∈ w) =
    (@w. w ∈ v ∧ (c.eval a2 e) ∈ w))
  ⇒ external v c ≅ c -: chu w
Proof
  strip_tac
  \\ simp[external_def]
  \\ qmatch_goalsub_abbrev_tac`cf_external b`
  \\ `b = {c.agent}`
  by (
    simp[Abbr`b`, fn_partition_def]
    \\ simp[Once SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS]
    \\ fs[GSYM MEMBER_NOT_EMPTY]
    \\ qexists_tac`x` \\ simp[]
    \\ conj_asm1_tac
    >- (
      qx_gen_tac`a` \\ strip_tac
      \\ simp[fn_part_def]
      \\ simp[Once EXTENSION]
      \\ qx_gen_tac`a2`
      \\ Cases_on`a2 ∈ c.agent` \\ simp[] )
    \\ metis_tac[] )
  \\ `b partitions c.agent`
  by (
    simp[partitions_thm, EXISTS_UNIQUE_ALT]
    \\ metis_tac[] )
  \\ `FINITE c.agent` by metis_tac[in_chu_objects, wf_def, finite_cf_def]
  \\ simp[iso_objs_thm]
  \\ qexists_tac`mk_chu_morphism (cf_external b c) c <|
       map_agent := λq. decode_function q (encode_set c.agent);
       map_env := λe. encode_pair (encode_set c.agent, e) |>`
  \\ conj_asm1_tac
  >- (
    gs[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[cf_external_def, mk_cf_def]
    \\ simp[repfns_def, PULL_EXISTS]
    \\ simp[restrict_def]
    \\ simp[is_repfn_def] )
  \\ simp[chu_iso_bij]
  \\ gs[maps_to_in_chu]
  \\ simp[mk_chu_morphism_def]
  \\ simp[cf_external_def, repfns_def]
  \\ simp[BIJ_DEF, INJ_DEF, SURJ_DEF, PULL_EXISTS, EXISTS_PROD]
  \\ simp[restrict_def]
  \\ simp[is_repfn_def]
  \\ simp[extensional_def, PULL_EXISTS]
  \\ rw[]
  \\ qexists_tac`λs. if s = c.agent then x else ARB`
  \\ rw[]
QED

Theorem external_idem:
  c ∈ chu_objects w ∧ v partitions w ⇒
  external v (external v c) ≅ external v c -: chu w
Proof
  strip_tac
  \\ irule equal_parts_external_iso
  \\ drule external_equal_parts
  \\ disch_then drule
  \\ strip_tac \\ simp[]
QED

Theorem external_mod_unequal_parts:
  c ∈ chu_objects w ∧ v partitions w ⇒
  (∀a1 a2.
    a1 ∈ (external_mod v c).agent ∧
    a2 ∈ (external_mod v c).agent ∧
    a1 ≠ a2 ⇒
    ∃e. e ∈ (external_mod v c).env ∧
    (@w. w ∈ v ∧ ((external_mod v c).eval a1 e) ∈ w) ≠
    (@w. w ∈ v ∧ ((external_mod v c).eval a2 e) ∈ w))
Proof
  rw[external_mod_def]
  \\ qmatch_goalsub_abbrev_tac`cf_external_mod b`
  \\ simp[Once cf_external_mod_def, PULL_EXISTS, EXISTS_PROD]
  \\ `∃q. q ∈ repfns b`
  by (
    rw[repfns_def, is_repfn_def]
    \\ qexists_tac`restrict (λx. @a. a ∈ x) b`
    \\ simp[]
    \\ rw[restrict_def]
    \\ SELECT_ELIM_TAC \\ rw[]
    \\ fs[Abbr`b`, fn_partition_def]
    \\ simp[fn_part_def]
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[] )
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ `FINITE c.agent` by metis_tac[in_chu_objects, wf_def, finite_cf_def]
  \\ `FINITE b ∧ EVERY_FINITE b`
  by (
    simp[Abbr`b`]
    \\ irule FINITE_fn_partition
    \\ rw[] )
  \\ fs[cf_external_mod_def, mk_cf_def]
  \\ fs[repfns_def]
  \\ BasicProvers.VAR_EQ_TAC
  \\ qmatch_assum_rename_tac`is_repfn b q`
  \\ `q x ∈ x ∧ q x' ∈ x'` by metis_tac[is_repfn_def]
  \\ `x ≠ x'` by metis_tac[decode_encode_set]
  \\ simp[restrict_def]
  \\ simp[Once(METIS_PROVE[]``(a ∧ b) ⇔ (a ∧ (a ⇒ b))``)]
  \\ reverse CASE_TAC >- metis_tac[]
  \\ reverse CASE_TAC >- metis_tac[]
  \\ ntac 2 (pop_assum kall_tac)
  \\ `∃a. a ∈ c.agent ∧ x = fn_part c.agent c.env c.eval v a`
  by (fs[Abbr`b`, fn_partition_def] \\ metis_tac[])
  \\ `∃a'. a' ∈ c.agent ∧ x' = fn_part c.agent c.env c.eval v a'`
  by (fs[Abbr`b`, fn_partition_def] \\ metis_tac[])
  \\ `a ≠ a'` by metis_tac[]
  \\ qmatch_assum_abbrev_tac`qx ∈ x`
  \\ qmatch_assum_abbrev_tac`qx' ∈ x'`
  \\ fs[fn_part_def]
  \\ Cases_on`c.env = ∅` \\ fs[]
  \\ Cases_on`∀e. e ∈ c.env ⇒ (@w. w ∈ v ∧ c.eval qx e ∈ w) =
                               (@w. w ∈ v ∧ c.eval qx' e ∈ w)`
  >- (
    fs[GSYM MEMBER_NOT_EMPTY]
    \\ first_x_assum drule
    \\ metis_tac[] )
  \\ metis_tac[]
QED

Theorem unequal_parts_external_mod_iso:
  c ∈ chu_objects w ∧ v partitions w ∧
  (∀a1 a2. a1 ∈ c.agent ∧ a2 ∈ c.agent ∧ a1 ≠ a2 ⇒
     ∃e. e ∈ c.env ∧ (@w. w ∈ v ∧ c.eval a1 e ∈ w) ≠
                     (@w. w ∈ v ∧ c.eval a2 e ∈ w))
  ⇒
  external_mod v c ≅ c -: chu w
Proof
  strip_tac
  \\ simp[external_mod_def]
  \\ qmatch_goalsub_abbrev_tac`cf_external_mod b`
  \\ `∀x. x ∈ b ⇒ SING x`
  by (
    simp[Abbr`b`, fn_partition_def, PULL_EXISTS]
    \\ qx_gen_tac`x` \\ strip_tac
    \\ simp[SING_DEF]
    \\ qexists_tac`x`
    \\ simp[fn_part_def]
    \\ simp[Once SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS]
    \\ rw[] \\ CCONTR_TAC
    \\ res_tac
    \\ gs[])
  \\ `∃!q. is_repfn b q`
  by (
    simp[EXISTS_UNIQUE_ALT]
    \\ simp[is_repfn_def]
    \\ qexists_tac`restrict (λx. @a. a ∈ x) b`
    \\ rw[EQ_IMP_THM] \\ rw[]
    \\ rw[restrict_def, FUN_EQ_THM]
    \\ gs[extensional_def, SING_DEF] \\ rw[]
    \\ res_tac \\ gs[]
    \\ metis_tac[IN_SING] )
  \\ `b partitions c.agent`
  by (
    simp[Abbr`b`]
    \\ irule partitions_fn_partition
    \\ metis_tac[in_chu_objects, wf_def] )
  \\ `∀q. is_repfn b q ⇒ BIJ q b c.agent`
  by (
    rw[is_repfn_def]
    \\ simp[BIJ_DEF, INJ_DEF, SURJ_DEF]
    \\ fs[partitions_thm, SUBSET_DEF]
    \\ metis_tac[IN_SING, SING_DEF] )
  \\ `SING (repfns b)`
  by (
    rw[repfns_def, SING_DEF]
    \\ simp[Once EXTENSION, PULL_EXISTS]
    \\ fs[EXISTS_UNIQUE_ALT]
    \\ metis_tac[] )
  \\ `FINITE b ∧ EVERY_FINITE b`
  by (
    simp[Abbr`b`]
    \\ irule FINITE_fn_partition
    \\ metis_tac[in_chu_objects, wf_def, finite_cf_def] )
  \\ fs[SING_DEF]
  \\ simp[iso_objs_thm]
  \\ qexists_tac`mk_chu_morphism (cf_external_mod b c) c <| map_agent := decode_function x;
  map_env := λe. encode_pair (x, e) |>`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[cf_external_mod_def, PULL_EXISTS, mk_cf_def]
    \\ reverse conj_tac >- metis_tac[]
    \\ `x ∈ repfns b` by metis_tac[IN_SING, EXTENSION]
    \\ fs[Once repfns_def]
    \\ simp[restrict_def]
    \\ fs[is_repfn_def]
    \\ qx_gen_tac`z`
    \\ reverse(rw[]) >- metis_tac[]
    \\ `z ⊆ c.agent` suffices_by metis_tac[SUBSET_DEF]
    \\ qpat_x_assum`z ∈ _`mp_tac
    \\ simp[Abbr`b`, fn_partition_def, PULL_EXISTS]
    \\ rpt strip_tac
    \\ simp[SUBSET_DEF, fn_part_def] )
  \\ simp[chu_iso_bij]
  \\ fs[maps_to_in_chu]
  \\ simp[mk_chu_morphism_def]
  \\ simp[cf_external_mod_def]
  \\ fs[is_chu_morphism_def, mk_chu_morphism_def, restrict_def]
  \\ fs[cf_external_mod_def, PULL_EXISTS, mk_cf_def]
  \\ simp[BIJ_DEF, INJ_DEF, SURJ_DEF, PULL_EXISTS, EXISTS_PROD]
  \\ `x ∈ repfns b` by metis_tac[IN_SING, EXTENSION]
  \\ pop_assum mp_tac
  \\ simp_tac(srw_ss())[repfns_def]
  \\ strip_tac
  \\ simp[]
  \\ simp[restrict_def]
  \\ `BIJ q b c.agent` by metis_tac[]
  \\ fs[BIJ_DEF, INJ_DEF, SURJ_DEF]
  \\ metis_tac[decode_encode_set]
QED

Theorem external_mod_idem:
  c ∈ chu_objects w ∧ v partitions w ⇒
  external_mod v (external_mod v c) ≅ external_mod v c -: chu w
Proof
  strip_tac
  \\ irule unequal_parts_external_mod_iso
  \\ drule external_mod_unequal_parts
  \\ disch_then drule
  \\ strip_tac \\ simp[]
QED

Theorem internal_equal_parts:
  c ∈ chu_objects w ∧ v partitions w ⇒
  (internal v c).env ≠ ∅ ∧
  (∀a e1 e2.
    e1 ∈ (internal v c).env ∧
    e2 ∈ (internal v c).env ∧
    a ∈ (internal v c).agent
    ⇒
    (@w. w ∈ v ∧ ((internal v c).eval a e1) ∈ w) =
    (@w. w ∈ v ∧ ((internal v c).eval a e2) ∈ w))
Proof
  strip_tac
  \\ fs[Once (GSYM swap_in_chu_objects), Excl"swap_in_chu_objects"]
  \\ drule external_equal_parts
  \\ disch_then drule
  \\ simp[GSYM swap_internal]
QED

Theorem equal_parts_internal_iso:
  c ∈ chu_objects w ∧ v partitions w ∧
  c.env ≠ ∅ ∧
  (∀e1 e2 a.
    e1 ∈ c.env ∧ e2 ∈ c.env ∧ a ∈ c.agent ⇒
    (@w. w ∈ v ∧ (c.eval a e1) ∈ w) =
    (@w. w ∈ v ∧ (c.eval a e2) ∈ w))
  ⇒ internal v c ≅ c -: chu w
Proof
  strip_tac
  \\ fs[Once (GSYM swap_in_chu_objects), Excl"swap_in_chu_objects"]
  \\ drule equal_parts_external_iso
  \\ disch_then drule
  \\ simp[GSYM swap_internal]
QED

Theorem internal_idem:
  c ∈ chu_objects w ∧ v partitions w ⇒
  internal v (internal v c) ≅ internal v c -: chu w
Proof
  strip_tac
  \\ irule equal_parts_internal_iso
  \\ drule internal_equal_parts
  \\ disch_then drule
  \\ strip_tac \\ simp[]
QED

Theorem internal_mod_unequal_parts:
  c ∈ chu_objects w ∧ v partitions w ⇒
  (∀e1 e2.
    e1 ∈ (internal_mod v c).env ∧
    e2 ∈ (internal_mod v c).env ∧
    e1 ≠ e2 ⇒
    ∃a. a ∈ (internal_mod v c).agent ∧
    (@w. w ∈ v ∧ ((internal_mod v c).eval a e1) ∈ w) ≠
    (@w. w ∈ v ∧ ((internal_mod v c).eval a e2) ∈ w))
Proof
  strip_tac
  \\ fs[Once (GSYM swap_in_chu_objects), Excl"swap_in_chu_objects"]
  \\ drule external_mod_unequal_parts
  \\ disch_then drule
  \\ simp[GSYM swap_internal_mod]
QED

Theorem unequal_parts_internal_mod_iso:
  c ∈ chu_objects w ∧ v partitions w ∧
  (∀e1 e2. e1 ∈ c.env ∧ e2 ∈ c.env ∧ e1 ≠ e2 ⇒
     ∃a. a ∈ c.agent ∧ (@w. w ∈ v ∧ c.eval a e1 ∈ w) ≠
                       (@w. w ∈ v ∧ c.eval a e2 ∈ w))
  ⇒
  internal_mod v c ≅ c -: chu w
Proof
  strip_tac
  \\ fs[Once (GSYM swap_in_chu_objects), Excl"swap_in_chu_objects"]
  \\ drule unequal_parts_external_mod_iso
  \\ disch_then drule
  \\ simp[GSYM swap_internal_mod]
QED

Theorem internal_mod_idem:
  c ∈ chu_objects w ∧ v partitions w ⇒
  internal_mod v (internal_mod v c) ≅ internal_mod v c -: chu w
Proof
  strip_tac
  \\ irule unequal_parts_internal_mod_iso
  \\ drule internal_mod_unequal_parts
  \\ disch_then drule
  \\ strip_tac \\ simp[]
QED

val _ = export_theory();
