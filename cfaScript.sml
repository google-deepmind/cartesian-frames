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
  pairTheory pred_setTheory listTheory rich_listTheory indexedListsTheory
  arithmeticTheory sortingTheory helperSetTheory categoryTheory
  cf0Theory cf1Theory cf2Theory cf3Theory cf5Theory cf6Theory cf9Theory

val _ = new_theory"cfa";

(* TODO: these could probably move back to an earlier theory *)

Theorem EXISTS_UNIQUE_EQ_inv:
  (∀x. P x ⇒ Q (f x)) ∧
  (∀x. Q x ⇒ P (g x)) ∧
  (∀x. f (g x) = x) ∧
  (∀x. g (f x) = x)
  ⇒
  ((∃!x. P x) ⇔ (∃!x. Q x))
Proof
  rw[EXISTS_UNIQUE_ALT]
  \\ EQ_TAC \\ rw[]
  >- (
    qexists_tac`f x` \\ rw[]
    \\ EQ_TAC \\ rw[]
    >- (
      `P (g y)` by metis_tac[]
      \\ first_x_assum(qspec_then`g y`mp_tac)
      \\ simp[] )
    >- (
      first_x_assum irule
      \\ first_x_assum(qspec_then`x`mp_tac)
      \\ simp[] ))
  \\ qexists_tac`g x`
  \\ rw[EQ_IMP_THM]
  >- (
    `Q (f y)` by metis_tac[]
    \\ res_tac
    \\ metis_tac[] )
  \\ first_x_assum irule
  \\ first_x_assum(qspec_then`x`mp_tac)
  \\ simp[]
QED

Definition assoc_upto_iso_def:
  assoc_upto_iso f ⇔
  ∀w c1 c2 c3.
    c1 ∈ chu_objects w ∧
    c2 ∈ chu_objects w ∧
    c3 ∈ chu_objects w
    ⇒
    f c1 (f c2 c3) ≅ f (f c1 c2) c3 -: chu w
End

Definition comm_upto_iso_def:
  comm_upto_iso f ⇔
  ∀w c1 c2.
    c1 ∈ chu_objects w ∧
    c2 ∈ chu_objects w ⇒
    f c1 c2 ≅ f c2 c1 -: chu w
End

Definition cong_upto_iso_def:
  cong_upto_iso f ⇔
  ∀w c1 c2 c3 c4.
    c1 ≅ c2 -: chu w ∧
    c3 ≅ c4 -: chu w
    ⇒
    f c1 c3 ≅ f c2 c4 -: chu w
End

Theorem prod_assoc_upto_iso[simp]:
  assoc_upto_iso prod
Proof
  rw[assoc_upto_iso_def]
  \\ metis_tac[prod_assoc]
QED

Theorem prod_comm_upto_iso[simp]:
  comm_upto_iso prod
Proof
  rw[comm_upto_iso_def]
  \\ metis_tac[prod_comm]
QED

Theorem sum_cong_upto_iso[simp]:
  cong_upto_iso sum
Proof
  rw[cong_upto_iso_def]
  \\ fs[iso_objs_thm]
  \\ qmatch_assum_rename_tac`f1 :- c1 → c2 -: _`
  \\ qmatch_assum_rename_tac`f2 :- c3 → c4 -: _`
  \\ qexists_tac`mk_chu_morphism (sum c1 c3) (sum c2 c4)
       <| map_agent := λa.
            sum_CASE (decode_sum a)
              (encode_sum o INL o f1.map.map_agent)
              (encode_sum o INR o f2.map.map_agent);
          map_env := encode_pair o pair$## f1.map.map_env f2.map.map_env o decode_pair |>`
  \\ conj_asm1_tac
  >- (
    fs[maps_to_in_chu]
    \\ fs[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[sum_def, mk_cf_def, PULL_EXISTS, EXISTS_PROD]
    \\ conj_tac >- (rw[] \\ rw[])
    \\ rw[sum_eval_def] \\ rw[] \\ gs[])
  \\ fs[chu_iso_bij, maps_to_in_chu]
  \\ gs[is_chu_morphism_def, mk_chu_morphism_def, restrict_def]
  \\ conj_tac
  >- (
    simp[BIJ_DEF, INJ_DEF, SURJ_DEF]
    \\ gs[sum_def, PULL_EXISTS, EXISTS_PROD]
    \\ conj_tac
    >- ( rw[] \\ gs[] \\ PROVE_TAC[BIJ_DEF, INJ_DEF] )
    \\ gen_tac
    \\ fs[BIJ_DEF, SURJ_DEF]
    \\ strip_tac \\ last_x_assum drule \\ strip_tac
    \\ gvs[]
    >- ( qexists_tac`encode_sum (INL y)` \\ simp[] )
    >- ( qexists_tac`encode_sum (INR y)` \\ simp[] ))
  \\ simp[BIJ_DEF, INJ_DEF, SURJ_DEF]
  \\ gs[sum_def, PULL_EXISTS, EXISTS_PROD]
  \\ conj_tac >- PROVE_TAC[BIJ_DEF, INJ_DEF]
  \\ fs[BIJ_DEF, SURJ_DEF]
  \\ metis_tac[]
QED

Theorem prod_cong_upto_iso[simp]:
  cong_upto_iso prod
Proof
  metis_tac[cong_upto_iso_def, sum_cong_upto_iso, swap_sum_prod, swap_iso]
QED

Theorem tensor_assoc_upto_iso[simp]:
  assoc_upto_iso tensor
Proof
  metis_tac[tensor_assoc, assoc_upto_iso_def]
QED

Theorem tensor_comm_upto_iso[simp]:
  comm_upto_iso tensor
Proof
  metis_tac[tensor_comm, comm_upto_iso_def]
QED

Theorem tensor_cong_upto_iso[simp]:
  cong_upto_iso tensor
Proof
  metis_tac[cong_upto_iso_def, iso_tensor]
QED

Theorem FOLDL_PERM_iso:
  comm_upto_iso f ∧ assoc_upto_iso f ∧ cong_upto_iso f ∧
  PERM l1 l2 ∧
  EVERY (λc. c ∈ chu_objects w) l1 ∧
  e1 ≅ e2 -: chu w
  ⇒
  FOLDL f e1 l1 ≅ FOLDL f e2 l2 -: chu w
Proof
  simp[GSYM AND_IMP_INTRO]
  \\ ntac 4 strip_tac
  \\ map_every qid_spec_tac[`e2`, `e1`]
  \\ pop_assum mp_tac
  \\ map_every qid_spec_tac [`l2`,`l1`]
  \\ ho_match_mp_tac PERM_STRONG_IND
  \\ conj_tac >- simp[]
  \\ rpt strip_tac \\ fs[]
  >- ( first_x_assum irule \\ fs[cong_upto_iso_def] )
  \\ `e1 ∈ chu_objects w ∧ e2 ∈ chu_objects w`
  by metis_tac[iso_objs_thm, maps_to_in_chu, is_category_chu]
  >- PROVE_TAC[assoc_upto_iso_def, comm_upto_iso_def, cong_upto_iso_def,
               is_category_chu, iso_objs_refl, chu_obj,
               iso_objs_trans, iso_objs_sym]
  \\ irule iso_objs_trans \\ fs[]
  \\ qexists_tac`FOLDL f e1 l1'`
  \\ simp[]
  \\ first_x_assum irule \\ simp[]
  \\ fs[EVERY_MEM]
  \\ metis_tac[MEM_PERM]
QED

Theorem FOLDL_iso_FOLDR:
  assoc_upto_iso f ∧ comm_upto_iso f ∧ cong_upto_iso f ∧
  LIST_REL (λc1 c2. c1 ≅ c2 -: chu w) l1 l2  ∧
  e1 ≅ e2 -: chu w
  ⇒
  FOLDL f e1 l1 ≅ FOLDR f e2 l2 -: chu w
Proof
  simp[GSYM AND_IMP_INTRO]
  \\ ntac 3 strip_tac
  \\ map_every qid_spec_tac[`e2`,`e1`,`l2`,`l1`]
  \\ Induct \\ rw[] \\ rw[]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ strip_tac
  \\ irule iso_objs_trans \\ simp[]
  \\ qexists_tac`f c2 (FOLDL f e1 l1)`
  \\ reverse conj_tac
  >- metis_tac[cong_upto_iso_def, iso_objs_sym, maps_to_in_chu,
               iso_objs_thm, iso_objs_refl, chu_obj, is_category_chu]
  \\ pop_assum kall_tac
  \\ `EVERY (λc. c ∈ chu_objects w) l1`
  by (
    gs[EVERY2_EVERY, EVERY_MEM, MEM_ZIP, PULL_EXISTS]
    \\ simp[MEM_EL, PULL_EXISTS]
    \\ metis_tac[iso_objs_thm, maps_to_in_chu, is_category_chu] )
  \\ ntac 2 (pop_assum mp_tac) \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ map_every qid_spec_tac[`e2`,`e1`,`h`,`c2`,`l1`]
  \\ Induct \\ rw[]
  >- metis_tac[cong_upto_iso_def, comm_upto_iso_def, iso_objs_trans, is_category_chu, iso_objs_sym, iso_objs_thm, maps_to_in_chu]
  \\ irule iso_objs_trans \\ simp[]
  \\ qexists_tac`FOLDL f (f (f e1 h) h') l1`
  \\ reverse conj_tac
  >- (
    first_x_assum irule
    \\ simp[]
    \\ metis_tac[cong_upto_iso_def, iso_objs_refl, chu_obj, is_category_chu])
  \\ irule FOLDL_PERM_iso \\ simp[]
  \\ `h' ∈ chu_objects w ∧ e1 ∈ chu_objects w`
  by metis_tac[iso_objs_thm, maps_to_in_chu, is_category_chu]
  \\ PROVE_TAC[assoc_upto_iso_def, comm_upto_iso_def, cong_upto_iso_def,
               is_category_chu, iso_objs_refl, chu_obj,
               iso_objs_trans, iso_objs_sym]
QED

Definition assoc_upto_equiv_def:
  assoc_upto_equiv f ⇔
  ∀w c1 c2 c3.
    c1 ∈ chu_objects w ∧
    c2 ∈ chu_objects w ∧
    c3 ∈ chu_objects w
    ⇒
    f c1 (f c2 c3) ≃ f (f c1 c2) c3 -: w
End

Definition comm_upto_equiv_def:
  comm_upto_equiv f ⇔
  ∀w c1 c2.
    c1 ∈ chu_objects w ∧
    c2 ∈ chu_objects w ⇒
    f c1 c2 ≃ f c2 c1 -: w
End

Theorem assoc_upto_iso_equiv:
  assoc_upto_iso f ⇒ assoc_upto_equiv f
Proof
  rw[assoc_upto_iso_def, assoc_upto_equiv_def]
  \\ metis_tac[iso_homotopy_equiv]
QED

Theorem comm_upto_iso_equiv:
  comm_upto_iso f ⇒ comm_upto_equiv f
Proof
  rw[comm_upto_iso_def, comm_upto_equiv_def]
  \\ metis_tac[iso_homotopy_equiv]
QED

Definition cong_upto_equiv_def:
  cong_upto_equiv f ⇔
  ∀w c1 c2 c3 c4.
    c1 ≃ c2 -: w ∧
    c3 ≃ c4 -: w
    ⇒
    f c1 c3 ≃ f c2 c4 -: w
End

Theorem prod_assoc_upto_equiv[simp]:
  assoc_upto_equiv prod
Proof
  metis_tac[assoc_upto_iso_equiv, prod_assoc_upto_iso]
QED

Theorem prod_comm_upto_equiv[simp]:
  comm_upto_equiv prod
Proof
  metis_tac[comm_upto_iso_equiv, prod_comm_upto_iso]
QED

Theorem sum_cong_upto_equiv[simp]:
  cong_upto_equiv sum
Proof
  rw[cong_upto_equiv_def]
  \\ metis_tac[homotopy_equiv_sum, homotopy_equiv_def, maps_to_in_chu]
QED

Theorem prod_cong_upto_equiv[simp]:
  cong_upto_equiv prod
Proof
  mp_tac sum_cong_upto_equiv
  \\ rw[cong_upto_equiv_def, Excl"sum_cong_upto_equiv"]
  \\ rw[GSYM swap_sum_prod]
  \\ DEP_REWRITE_TAC[homotopy_equiv_swap]
  \\ DEP_REWRITE_TAC[sum_in_chu_objects]
  \\ simp[]
  \\ conj_asm1_tac >- metis_tac[homotopy_equiv_def, maps_to_in_chu]
  \\ fs[]
QED

Theorem FOLDL_PERM_equiv:
  comm_upto_equiv f ∧ assoc_upto_equiv f ∧ cong_upto_equiv f ∧
  PERM l1 l2 ∧
  EVERY (λc. c ∈ chu_objects w) l1 ∧
  e1 ≃ e2 -: w
  ⇒
  FOLDL f e1 l1 ≃ FOLDL f e2 l2 -: w
Proof
  simp[GSYM AND_IMP_INTRO]
  \\ ntac 4 strip_tac
  \\ map_every qid_spec_tac[`e2`, `e1`]
  \\ pop_assum mp_tac
  \\ map_every qid_spec_tac [`l2`,`l1`]
  \\ ho_match_mp_tac PERM_STRONG_IND
  \\ conj_tac >- simp[]
  \\ rpt strip_tac \\ fs[]
  >- ( first_x_assum irule \\ fs[cong_upto_equiv_def] )
  \\ `e1 ∈ chu_objects w ∧ e2 ∈ chu_objects w`
  by metis_tac[homotopy_equiv_def, maps_to_in_chu]
  >- PROVE_TAC[assoc_upto_equiv_def, comm_upto_equiv_def, cong_upto_equiv_def,
               homotopy_equiv_refl, homotopy_equiv_trans, homotopy_equiv_sym]
  \\ irule homotopy_equiv_trans \\ fs[]
  \\ qexists_tac`FOLDL f e1 l1'`
  \\ simp[]
  \\ first_x_assum irule \\ simp[]
  \\ fs[EVERY_MEM]
  \\ metis_tac[MEM_PERM]
QED

Theorem FOLDL_equiv_FOLDR:
  assoc_upto_equiv f ∧ comm_upto_equiv f ∧ cong_upto_equiv f ∧
  LIST_REL (λc1 c2. c1 ≃ c2 -: w) l1 l2  ∧
  e1 ≃ e2 -: w
  ⇒
  FOLDL f e1 l1 ≃ FOLDR f e2 l2 -: w
Proof
  simp[GSYM AND_IMP_INTRO]
  \\ ntac 3 strip_tac
  \\ map_every qid_spec_tac[`e2`,`e1`,`l2`,`l1`]
  \\ Induct \\ rw[] \\ rw[]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ strip_tac
  \\ irule homotopy_equiv_trans \\ simp[]
  \\ qexists_tac`f c2 (FOLDL f e1 l1)`
  \\ reverse conj_tac
  >- metis_tac[cong_upto_equiv_def, homotopy_equiv_sym, maps_to_in_chu,
               homotopy_equiv_def, homotopy_equiv_refl]
  \\ pop_assum kall_tac
  \\ `EVERY (λc. c ∈ chu_objects w) l1`
  by (
    gs[EVERY2_EVERY, EVERY_MEM, MEM_ZIP, PULL_EXISTS]
    \\ simp[MEM_EL, PULL_EXISTS]
    \\ metis_tac[homotopy_equiv_def, maps_to_in_chu] )
  \\ ntac 2 (pop_assum mp_tac) \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ map_every qid_spec_tac[`e2`,`e1`,`h`,`c2`,`l1`]
  \\ Induct \\ rw[]
  >- metis_tac[cong_upto_equiv_def, comm_upto_equiv_def, homotopy_equiv_trans, homotopy_equiv_sym, homotopy_equiv_def, maps_to_in_chu]
  \\ irule homotopy_equiv_trans \\ simp[]
  \\ qexists_tac`FOLDL f (f (f e1 h) h') l1`
  \\ reverse conj_tac
  >- (
    first_x_assum irule
    \\ simp[]
    \\ metis_tac[cong_upto_equiv_def, homotopy_equiv_refl])
  \\ irule FOLDL_PERM_equiv \\ simp[]
  \\ `h' ∈ chu_objects w ∧ e1 ∈ chu_objects w`
  by metis_tac[homotopy_equiv_def, maps_to_in_chu]
  \\ PROVE_TAC[assoc_upto_equiv_def, comm_upto_equiv_def, cong_upto_equiv_def,
               homotopy_equiv_refl, homotopy_equiv_trans, homotopy_equiv_sym]
QED

Theorem image_sum:
  image (sum c1 c2) =
  if (c1.env = ∅ ∨ c2.env = ∅) then ∅ else
  image c1 ∪ image c2
Proof
  rw[image_def, sum_def, PULL_EXISTS, EXISTS_PROD, mk_cf_def]
  \\ rw[EXTENSION, EQ_IMP_THM, sum_eval_def] \\ rw[]
  \\ dsimp[]
  \\ metis_tac[MEMBER_NOT_EMPTY]
QED

Theorem image_prod:
  image (prod c1 c2) =
  if (c1.agent = ∅ ∨ c2.agent = ∅) then ∅ else
  image c1 ∪ image c2
Proof
  simp[GSYM swap_sum_prod]
  \\ simp[image_sum]
QED

Theorem FOLDL_prod_agent:
  (FOLDL prod e ls).agent =
  FOLDL (λa1 a2. IMAGE encode_pair (a1 × a2)) e.agent (MAP (λc. c.agent) ls)
Proof
  qid_spec_tac`e`
  \\ Induct_on`ls` \\ rw[]
  \\ rw[prod_def]
QED

Theorem FOLDL_prod_env:
  (FOLDL prod e ls).env =
  FOLDL (λe1 e2. IMAGE encode_sum (IMAGE INL e1 ∪ IMAGE INR e2)) e.env
  (MAP (λc. c.env) ls)
Proof
  qid_spec_tac`e`
  \\ Induct_on`ls` \\ rw[]
  \\ rw[prod_def]
QED

Theorem IN_FOLDL_prod_env:
  (e ∈ (FOLDL prod x ls).env ⇔
   e ∈ IMAGE (FUNPOW (encode_sum o INL) (LENGTH ls)) x.env ∨
   ∃n. (n < LENGTH ls) ∧
       e ∈ IMAGE (FUNPOW (encode_sum o INL) (LENGTH ls - n - 1) o encode_sum o INR) (EL n ls).env)
Proof
  map_every qid_spec_tac[`x`,`ls`]
  \\ Induct \\ simp[]
  \\ simp[prod_def, PULL_EXISTS]
  \\ rpt gen_tac
  \\ eq_tac \\ strip_tac \\ gs[FUNPOW]
  >- metis_tac[]
  >- (
    disj2_tac
    \\ qexists_tac`0`
    \\ simp[] \\ metis_tac[] )
  >- (
    disj2_tac
    \\ qexists_tac`SUC n`
    \\ simp[ADD1]
    \\ metis_tac[] )
  >- metis_tac[]
  >- (
    Cases_on`n` \\ fs[]
    >- metis_tac[]
    \\ fs[ADD1]
    \\ metis_tac[])
QED

Theorem image_FOLDL_prod:
  image (FOLDL prod e ls) =
  if EXISTS (λc. c.agent = ∅) (e :: ls) then ∅
  else BIGUNION (set (MAP image (e :: ls)))
Proof
  map_every qid_spec_tac[`e`,`ls`]
  \\ ho_match_mp_tac SNOC_INDUCT
  \\ rw[]
  >- rw[image_def]
  \\ simp[FOLDL_SNOC, EXISTS_SNOC, MAP_SNOC, LIST_TO_SET_SNOC]
  \\ simp[image_prod]
  \\ Cases_on`x.agent = ∅` \\ simp[]
  \\ simp[FOLDL_prod_agent]
  \\ simp[FOLDL_MAP]
  \\ qmatch_goalsub_abbrev_tac`COND b`
  \\ `b ⇔ EXISTS (λc. c.agent = ∅) (e::ls)`
  by (
    simp[Abbr`b`]
    \\ qid_spec_tac`e`
    \\ rpt(pop_assum kall_tac)
    \\ Induct_on`ls`
    \\ rw[]
    \\ first_x_assum(qspec_then`prod e h`mp_tac)
    \\ rw[prod_def]
    \\ simp[CROSS_EMPTY_EQN]
    \\ metis_tac[] )
  \\ simp[Abbr`b`]
  \\ Cases_on`e.agent = ∅` \\ simp[]
  \\ IF_CASES_TAC \\ simp[]
  \\ metis_tac[UNION_COMM, UNION_ASSOC]
QED

Theorem FOLDL_prod_in_chu_objects[simp]:
  c ∈ chu_objects w ∧
  EVERY (λc. c ∈ chu_objects w) cs
  ⇒
  FOLDL prod c cs ∈ chu_objects w
Proof
  qid_spec_tac`c`
  \\ Induct_on`cs`
  \\ rw[]
QED

Theorem FOLDL_tensor_in_chu_objects[simp]:
  c ∈ chu_objects w ∧
  EVERY (λc. c ∈ chu_objects w) cs
  ⇒
  FOLDL tensor c cs ∈ chu_objects w
Proof
  qid_spec_tac`c`
  \\ Induct_on`cs`
  \\ rw[]
QED

Theorem image_cfT[simp]:
  image (cfT w) = ∅
Proof
  rw[image_def, cfT_def, cf0_def]
QED

Theorem image_assume_SUBSET:
  image (assume s c) ⊆ image c INTER s
Proof
  rw[image_def, assume_def, cf_assume_def, mk_cf_def, SUBSET_DEF]
  \\ rw[]
  \\ metis_tac[]
QED

Theorem partitions_DISJOINT:
  partitions v w ∧ s1 ∈ v ∧ s2 ∈ v ∧ s1 ≠ s2 ⇒
  DISJOINT s1 s2
Proof
  rw[partitions_thm, IN_DISJOINT]
  \\ fs[EXISTS_UNIQUE_ALT, SUBSET_DEF]
  \\ metis_tac[]
QED

Overload "⊗" = ``tensor``
val _ = set_fixity "⊗" (Infix (LEFT, 500))

(* -- *)

Definition obs_part_def:
  obs_part c = { v | partitions v c.world ∧ ∀s. s ∈ v ⇒ s ∈ obs c }
End

Theorem obs_obs_part:
  c ∈ chu_objects w ∧ s PSUBSET w ∧ s ≠ ∅ ⇒
  (s ∈ obs c ⇔ { s ; w DIFF s } ∈ obs_part c)
Proof
  strip_tac
  \\ rw[obs_part_def]
  \\ reverse eq_tac >- rw[]
  \\ strip_tac
  \\ conj_tac
  >- (
    simp[partitions_thm]
    \\ fs[in_chu_objects]
    \\ dsimp[EXISTS_UNIQUE_ALT]
    \\ gs[PSUBSET_EQN, SUBSET_DIFF_EMPTY]
    \\ rpt strip_tac
    \\ qexists_tac`if y ∈ s then s else w DIFF s`
    \\ gen_tac \\ EQ_TAC \\ IF_CASES_TAC \\ strip_tac \\ gs[]
    \\ BasicProvers.VAR_EQ_TAC
    \\ simp[] )
  \\ rpt strip_tac \\ simp[]
  \\ metis_tac[obs_compl, in_chu_objects]
QED

Theorem obs_part_conditional_policies:
  c ∈ chu_objects w ∧ w ≠ ∅ ⇒
  (v ∈ obs_part c ⇔
   partitions v w ∧
   ∀f. extensional f v ∧ IMAGE f v ⊆ c.agent ⇒
     ∃a. a ∈ c.agent ∧
       ∀e. e ∈ c.env ⇒
         c.eval (f (@s. s ∈ v ∧ c.eval a e ∈ s)) e = c.eval a e)
Proof
  strip_tac
  \\ simp[obs_part_def]
  \\ `c.world = w` by fs[in_chu_objects]
  \\ simp[]
  \\ Cases_on`partitions v w` \\ simp[]
  \\ imp_res_tac in_chu_objects_finite_world
  \\ `FINITE v ∧ EVERY_FINITE v` by metis_tac[partitions_FINITE]
  \\ Induct_on`CARD v`
  >- (
    rw[]
    \\ gs[CARD_EQ_0]
    \\ fs[partitions_thm]
    \\ metis_tac[MEMBER_NOT_EMPTY, EXISTS_UNIQUE_ALT])
  \\ rpt strip_tac
  \\ Cases_on`SING v`
  >- (
    `v = {w}`
    by (
      fs[partitions_thm, SING_DEF]
      \\ gvs[EXISTS_UNIQUE_ALT, SUBSET_DEF]
      \\ metis_tac[EXTENSION] )
    \\ `w ∈ obs c`
    by (
      simp[obs_def, ifs_def]
      \\ metis_tac[in_chu_objects, wf_def] )
    \\ simp[]
    \\ rpt strip_tac
    \\ qexists_tac`f w`
    \\ simp[]
    \\ rpt strip_tac
    \\ SELECT_ELIM_TAC
    \\ simp[]
    \\ metis_tac[in_chu_objects, wf_def] )
  \\ `∃s1 s2. s1 ∈ v ∧ s2 ∈ v ∧ s1 ≠ s2`
  by (
    Cases_on`v` \\ fs[]
    \\ Cases_on`t` \\ fs[]
    \\ metis_tac[] )
  \\ `s1 ∪ s2 ∉ v`
  by (
    fs[partitions_thm]
    \\ strip_tac
    \\ fs[EXISTS_UNIQUE_ALT, SUBSET_DEF]
    \\ last_x_assum(qspec_then`ARB`kall_tac)
    \\ metis_tac[MEMBER_NOT_EMPTY, IN_UNION] )
  \\ first_x_assum(qspec_then`s1 ∪ s2 INSERT (v DELETE s1 DELETE s2)`mp_tac)
  \\ impl_tac
  >- (
    simp[]
    \\ Cases_on`v` \\ gs[]
    \\ Cases_on`t` \\ gs[] )
  \\ impl_keep_tac
  >- (
    fs[partitions_thm]
    \\ conj_tac
    >- (rpt strip_tac \\ gs[])
    \\ rpt strip_tac
    \\ gs[EXISTS_UNIQUE_ALT]
    \\ metis_tac[IN_UNION] )
  \\ qmatch_assum_abbrev_tac`partitions v1 w`
  \\ impl_keep_tac >- metis_tac[partitions_FINITE]
  \\ impl_keep_tac >- metis_tac[partitions_FINITE]
  \\ strip_tac
  \\ eq_tac \\ strip_tac
  >- (
    `∀s. s ∈ v1 ⇒ s ∈ obs c`
    by (
      simp_tac(srw_ss())[Abbr`v1`]
      \\ reverse(rpt strip_tac) >- metis_tac[]
      \\ metis_tac[obs_union] )
    \\ fs[]
    \\ rpt strip_tac
    \\ first_x_assum(qspec_then`λs.
          if s = s1 ∪ s2 then f s2
          else if s = s1 ∨ s = s2 then ARB
          else f s` mp_tac)
    \\ impl_tac
    >- (
      gs[extensional_def, SUBSET_DEF, PULL_EXISTS, Abbr`v1`]
      \\ metis_tac[] )
    \\ strip_tac
    \\ qexists_tac`@b. b ∈ ifs c s1 (f s1) a`
    \\ SELECT_ELIM_TAC
    \\ conj_tac
    >- (
      `s1 ∈ obs c` by metis_tac[]
      \\ pop_assum mp_tac
      \\ simp_tac(srw_ss())[obs_def]
      \\ strip_tac
      \\ first_x_assum irule
      \\ fs[SUBSET_DEF, PULL_EXISTS] )
    \\ qx_gen_tac`b` \\ strip_tac
    \\ conj_asm1_tac >- fs[ifs_def]
    \\ rpt strip_tac
    \\ first_x_assum drule
    \\ strip_tac
    \\ Cases_on`c.eval a e ∈ s1`
    >- (
      fs[ifs_def]
      \\ first_x_assum(qspec_then`e`mp_tac)
      \\ simp[]
      \\ Cases_on`c.eval b e ∈ s1` \\ simp[]
      \\ strip_tac \\ fs[]
      \\ fs[partitions_thm, EXISTS_UNIQUE_ALT]
      \\ metis_tac[in_chu_objects, wf_def] )
    \\ Cases_on`c.eval a e ∈ s2`
    >- (
      fs[]
      \\ `(@s. s ∈ v1 ∧ c.eval a e ∈ s) = s1 ∪ s2`
      by (
        fs[partitions_thm, EXISTS_UNIQUE_ALT, Abbr`v1`, SUBSET_DEF]
        \\ metis_tac[] )
      \\ fs[]
      \\ fs[ifs_def]
      \\ first_x_assum(qspec_then`e`mp_tac)
      \\ simp[]
      \\ Cases_on`c.eval b e ∈ s1` \\ simp[]
      \\ strip_tac \\ fs[]
      \\ fs[partitions_thm, EXISTS_UNIQUE_ALT, SUBSET_DEF]
      \\ metis_tac[])
    \\ fs[]
    \\ qmatch_asmsub_abbrev_tac`vv = s1 ∪ s2`
    \\ fs[partitions_thm, EXISTS_UNIQUE_ALT]
    \\ fs[ifs_def, SUBSET_DEF, PULL_EXISTS]
    \\ `vv ≠ s1` by metis_tac[IN_UNION, IN_DELETE, in_chu_objects, wf_def]
    \\ `vv ≠ s2` by metis_tac[IN_UNION, IN_DELETE, in_chu_objects, wf_def]
    \\ `vv ≠ s1 ∪ s2` by metis_tac[IN_UNION, IN_DELETE, in_chu_objects, wf_def]
    \\ fs[]
    \\ Cases_on`c.eval b e ∈ s1` \\ gs[]
    >- metis_tac[]
    \\ first_x_assum(qspec_then`e`mp_tac) \\ simp[]
    \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`f v2`
    \\ `v2 = vv` suffices_by metis_tac[]
    \\ simp[Abbr`v2`, Abbr`vv`]
    \\ AP_TERM_TAC
    \\ simp[FUN_EQ_THM]
    \\ simp[Abbr`v1`]
    \\ metis_tac[IN_UNION])
  \\ simp[obs_def]
  \\ gen_tac \\ strip_tac
  \\ conj_asm1_tac >- metis_tac[partitions_thm]
  \\ rpt gen_tac \\ strip_tac
  \\ first_x_assum(qspec_then`restrict (λx. if x = s then a0 else a1) v`mp_tac)
  \\ simp[]
  \\ impl_tac
  >- ( simp[SUBSET_DEF, PULL_EXISTS, restrict_def] \\ rw[] )
  \\ strip_tac
  \\ simp[ifs_def]
  \\ qexists_tac`a`
  \\ fs[restrict_def]
  \\ gen_tac \\ strip_tac
  \\ first_x_assum(qspec_then`e`mp_tac)
  \\ fs[partitions_thm, SUBSET_DEF, EXISTS_UNIQUE_ALT]
  \\ metis_tac[in_chu_objects, wf_def]
QED

(* TODO: conditional policy example 2.1 *)

Definition obs_part_additive_def:
  obs_part_additive c = { v | partitions v c.world ∧
    let ss = SET_TO_LIST v in
    ∃f.
    EVERY (λs. f s ◁ cfbot c.world s -: c.world) ss ∧
    c ≃ FOLDL prod (cfT c.world) (MAP f ss) -: c.world }
End

Definition obs_part_assuming_def:
  obs_part_assuming c = { v | partitions v c.world ∧
    c ≃ FOLDL prod (cfT c.world)
          (MAP (flip assume c) (SET_TO_LIST v)) -: c.world }
End

Theorem obs_part_assuming_imp_additive[local]:
  obs_part_assuming c ⊆ obs_part_additive c
Proof
  rw[SUBSET_DEF, obs_part_additive_def, obs_part_assuming_def]
  \\ qexists_tac`flip assume c` \\ simp[]
  \\ `c ∈ chu_objects c.world` by metis_tac[homotopy_equiv_def, maps_to_in_chu]
  \\ imp_res_tac in_chu_objects_finite_world
  \\ imp_res_tac partitions_FINITE
  \\ simp[EVERY_MEM]
  \\ rpt strip_tac
  \\ irule assume_subagent_cfbot
  \\ fs[partitions_thm]
QED

Theorem obs_part_additive_imp[local]:
  obs_part_additive c ⊆ obs_part c
Proof
  rw[SUBSET_DEF, obs_part_additive_def, obs_part_def]
  \\ qmatch_assum_abbrev_tac`partitions _ w`
  \\ qmatch_assum_rename_tac`partitions v w`
  \\ `c ∈ chu_objects w` by imp_res_tac homotopy_equiv_in_chu_objects
  \\ imp_res_tac in_chu_objects_finite_world
  \\ drule partitions_FINITE
  \\ simp[] \\ strip_tac
  \\ `MEM s (SET_TO_LIST v)` by simp[]
  \\ fs[MEM_EL]
  \\ qmatch_assum_abbrev_tac`n < LENGTH ss`
  \\ qabbrev_tac `tf = λi. if i = n then LENGTH ss - 1
                           else if i = LENGTH ss - 1 then n
                           else i`
  \\ `tf PERMUTES (count (LENGTH ss))`
  by (
    simp[BIJ_IFF_INV]
    \\ conj_tac >- simp[Abbr`tf`]
    \\ qexists_tac`tf` \\ simp[Abbr`tf`] )
  \\ `PERM ss (GENLIST (λi. EL (tf i) ss) (LENGTH ss))`
  by metis_tac[PERM_BIJ_IFF]
  \\ qmatch_assum_abbrev_tac`PERM ss ss0`
  \\ `c ≃ FOLDL prod (cfT w) (MAP f ss0) -: w`
  by (
    irule homotopy_equiv_trans
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ irule FOLDL_PERM_equiv
    \\ simp[EVERY_MAP, EVERY_MEM, PERM_MAP]
    \\ simp[Abbr`ss`] \\ fs[EVERY_MEM]
    \\ metis_tac[subagent_def])
  \\ DEP_REWRITE_TAC[obs_homotopy_equiv_prod_subagent]
  \\ `∃sr. ss0 = SNOC s sr`
  by (
    qspec_then`ss0`FULL_STRUCT_CASES_TAC SNOC_CASES \\ fs[]
    \\ imp_res_tac PERM_LENGTH \\ fs[]
    \\ fs[GENLIST, Abbr`tf`] )
  \\ pop_assum SUBST_ALL_TAC
  \\ fs[FOLDL_SNOC, MAP_SNOC]
  \\ qmatch_assum_abbrev_tac`c ≃ c2 && c1 -: w`
  \\ `c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w`
  by (
    simp[Abbr`c1`, Abbr`c2`]
    \\ fs[EVERY_MEM, MEM_EL, PULL_EXISTS]
    \\ conj_tac >- metis_tac[subagent_def]
    \\ irule FOLDL_prod_in_chu_objects
    \\ simp[EVERY_MAP, EVERY_MEM, MEM_EL, PULL_EXISTS]
    \\ metis_tac[subagent_def, MEM_EL, MEM_PERM, MEM_SNOC])
  \\ `c ≃ c1 && c2 -:w`
  by metis_tac[homotopy_equiv_trans, iso_homotopy_equiv, prod_comm]
  \\ conj_tac >- metis_tac[partitions_thm]
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ fs[EVERY_MEM, MEM_EL, PULL_EXISTS]
  \\ conj_tac >- metis_tac[]
  \\ DEP_REWRITE_TAC[subagent_cfbot_image]
  \\ fs[Abbr`c2`]
  \\ simp[image_FOLDL_prod] \\ rw[]
  \\ simp[SUBSET_DEF, PULL_EXISTS, MEM_MAP]
  \\ simp[image_def, PULL_EXISTS]
  \\ `ALL_DISTINCT ss` by simp[Abbr`ss`]
  \\ imp_res_tac ALL_DISTINCT_PERM
  \\ imp_res_tac ALL_DISTINCT_SNOC
  \\ rpt gen_tac \\ strip_tac
  \\ qmatch_assum_rename_tac`MEM s1 sr`
  \\ `MEM s1 ss` by metis_tac[MEM_PERM, MEM_SNOC]
  \\ `f s1 ∈ chu_objects w` by metis_tac[MEM_EL, subagent_def]
  \\ conj_tac >- metis_tac[in_chu_objects, wf_def]
  \\ `f s1 ◁ cfbot w s1 -: w` by metis_tac[MEM_EL]
  \\ `s1 ⊆ w` by metis_tac[MEM_SET_TO_LIST, partitions_thm]
  \\ `image (f s1) ⊆ s1` by metis_tac[subagent_cfbot_image]
  \\ fs[image_def, SUBSET_DEF, PULL_EXISTS]
  \\ metis_tac[partitions_DISJOINT, IN_DISJOINT, MEM_SET_TO_LIST, MEM_EL]
QED

Theorem obs_part_imp_assuming[local]:
  c ∈ chu_objects w ∧ w ≠ ∅ ⇒
  obs_part c ⊆ obs_part_assuming c
Proof
  rw[SUBSET_DEF]
  \\ Cases_on`c.agent = ∅`
  >- (
    simp[obs_part_assuming_def]
    \\ gs[obs_part_def]
    \\ fs[obs_def]
    \\ drule partitions_FINITE
    \\ impl_tac >- metis_tac[in_chu_objects_finite_world, in_chu_objects]
    \\ strip_tac
    \\ Cases_on`x = ∅`
    >- (
      fs[partitions_thm, EXISTS_UNIQUE_THM]
      \\ `w = ∅` by metis_tac[in_chu_objects, GSYM MEMBER_NOT_EMPTY] )
    \\ `SET_TO_LIST x ≠ []` by (
      Cases_on`SET_TO_LIST x` \\ gs[SET_TO_LIST_THM] )
    \\ pop_assum mp_tac
    \\ Cases_on`c.env = ∅`
    >- (
      `c = null w` by  (
        simp[cf_component_equality]
        \\ fs[in_chu_objects]
        \\ fs[wf_def]
        \\ simp[FUN_EQ_THM] )
      \\ `∀h. assume h (null w) = null w`
      by (
        simp[cf_component_equality]
        \\ fs[in_chu_objects]
        \\ simp[assume_def]
        \\ simp[cf_assume_def, mk_cf_def, FUN_EQ_THM] )
      \\ qspec_tac(`SET_TO_LIST x`,`ls`)
      \\ Induct \\ simp[]
      \\ Cases_on`ls = []` \\ fs[]
      >- metis_tac[prod_cfT, iso_homotopy_equiv, homotopy_equiv_sym]
      \\ Cases_on`ls` \\ gs[]
      \\ irule homotopy_equiv_trans
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ irule iso_homotopy_equiv
      \\ irule FOLDL_PERM_iso
      \\ simp[EVERY_MAP]
      \\ imp_res_tac in_chu_objects_finite_world
      \\ irule iso_objs_trans \\ simp[]
      \\ qexists_tac`cfT w && (null w && null w)`
      \\ conj_tac >- (
        rewrite_tac[null_prod_null]
        \\ simp[] )
      \\ irule prod_assoc
      \\ simp[] )
    \\ drule empty_agent_nonempty_env
    \\ simp[] \\ strip_tac
    \\ imp_res_tac in_chu_objects \\ fs[]
    \\ `∀h. assume h c = c`
    by (
      simp[cf_component_equality]
      \\ simp[assume_def]
      \\ gs[wf_def]
      \\ simp[cf_assume_def, mk_cf_def, FUN_EQ_THM] )
    \\ qspec_tac(`SET_TO_LIST x`,`ls`)
    \\ Induct \\ simp[]
    \\ Cases_on`ls = []` \\ fs[]
    >- metis_tac[prod_cfT, iso_homotopy_equiv, homotopy_equiv_sym]
    \\ Cases_on`ls` \\ gs[]
    \\ irule homotopy_equiv_trans
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ irule FOLDL_PERM_equiv
    \\ simp[EVERY_MAP]
    \\ irule homotopy_equiv_trans
    \\ qexists_tac`c`
    \\ conj_tac >- metis_tac[prod_cfT, iso_homotopy_equiv]
    \\ irule homotopy_equiv_trans
    \\ qexists_tac`cfT w && (c && c)`
    \\ reverse conj_tac
    >- metis_tac[prod_assoc, iso_homotopy_equiv,
                 cfT_in_chu_objects, in_chu_objects_finite_world]
    \\ irule homotopy_equiv_trans
    \\ qexists_tac`c && c`
    \\ reverse conj_tac
    >- (
      simp[Once homotopy_equiv_sym]
      \\ irule iso_homotopy_equiv
      \\ irule (DISCH_ALL(CONJUNCT1(UNDISCH prod_cfT)))
      \\ simp[] )
    \\ irule homotopy_equiv_trans
    \\ qexists_tac`cf0 w` \\ simp[]
    \\ irule homotopy_equiv_trans
    \\ qexists_tac`cf0 w && cf0 w` \\ simp[]
    \\ conj_tac >- metis_tac[cf0_prod_cf0, homotopy_equiv_sym, in_chu_objects_finite_world]
    \\ irule homotopy_equiv_prod
    \\ imp_res_tac in_chu_objects_finite_world
    \\ simp[]
    \\ simp[homotopy_equiv_sym])
  \\ drule obs_part_conditional_policies
  \\ simp[]
  \\ disch_then(qspec_then`x`mp_tac)
  \\ simp[] \\ strip_tac
  \\ imp_res_tac in_chu_objects
  \\ simp[obs_part_assuming_def]
  \\ qmatch_goalsub_abbrev_tac`FOLDL prod ct cs`
  \\ `∀e. e ∈ c.env ⇒ ∃!s. s ∈ x ∧ e ∈ (assume s c).env`
  by (
    simp[EXISTS_UNIQUE_THM]
    \\ fs[obs_part_def]
    \\ `∃a. a ∈ c.agent` by metis_tac[MEMBER_NOT_EMPTY]
    \\ gen_tac \\ strip_tac
    \\ `c.eval a e ∈ w` by metis_tac[in_chu_objects, wf_def]
    \\ fs[partitions_thm]
    \\ `∃!s. s ∈ x ∧ c.eval a e ∈ s` by metis_tac[]
    \\ pop_assum mp_tac
    \\ simp_tac(srw_ss())[EXISTS_UNIQUE_THM]
    \\ strip_tac
    \\ simp[assume_def, cf_assume_def]
    \\ qexists_tac`s` \\ rw[]
    \\ fs[obs_def, ifs_def]
    \\ `c.eval a' e ∈ c.world` by metis_tac[in_chu_objects, wf_def]
    \\ `∃!s'. s' ∈ x ∧ c.eval a' e ∈ s'` by metis_tac[]
    \\ pop_assum mp_tac
    \\ simp_tac(srw_ss())[EXISTS_UNIQUE_THM]
    \\ strip_tac
    \\ Cases_on`s' = s` \\ fs[]
    \\ metis_tac[] )
  \\ drule partitions_FINITE
  \\ impl_keep_tac >- metis_tac[in_chu_objects_finite_world]
  \\ strip_tac
  \\ `∃fi. BIJ fi x (count (LENGTH cs)) ∧
           (∀s. s ∈ x ⇒ EL (fi s) cs = assume s c) ∧
           (∀n. (n < LENGTH cs) ⇒ fi (EL n (SET_TO_LIST x)) = n)`
  by (
    simp[Abbr`cs`]
    \\ qexists_tac`flip findi (SET_TO_LIST x)`
    \\ simp[BIJ_DEF, INJ_DEF, SURJ_DEF]
    \\ simp[MEM_findi]
    \\ `∀a. a ∈ x ⇔ (∃n. (n < LENGTH (SET_TO_LIST x)) ∧ EL n (SET_TO_LIST x) = a)`
    by metis_tac[MEM_EL, MEM_SET_TO_LIST]
    \\ simp[PULL_EXISTS]
    \\ simp[MEM_findi, findi_EL, EL_MAP]
    \\ metis_tac[findi_EL, ALL_DISTINCT_SET_TO_LIST] )
  \\ qabbrev_tac`ef = λe.
       let n = fi (@s. s ∈ x ∧ e ∈ (assume s c).env) in
       FUNPOW (encode_sum o INL) (LENGTH cs - n - 1) (encode_sum (INR e))`
  \\ `BIJ ef c.env (FOLDL prod ct cs).env`
  by (
    simp[BIJ_DEF, INJ_DEF, Abbr`ef`]
    \\ conj_asm1_tac
    >- (
      simp[IN_FOLDL_prod_env, PULL_EXISTS]
      \\ conj_tac
      >- (
        rpt strip_tac
        \\ disj2_tac
        \\ qmatch_goalsub_abbrev_tac`LENGTH cs - (n + 1)`
        \\ qexists_tac`n`
        \\ qexists_tac`e`
        \\ simp[]
        \\ simp[Abbr`n`]
        \\ SELECT_ELIM_TAC
        \\ conj_tac >- metis_tac[EXISTS_UNIQUE_ALT]
        \\ qx_gen_tac`s` \\ strip_tac
        \\ fs[BIJ_DEF, INJ_DEF] )
      \\ rpt gen_tac \\ strip_tac
      \\ qmatch_goalsub_abbrev_tac`FUNPOW _ n`
      \\ qmatch_goalsub_abbrev_tac`_ = FUNPOW _ n' _`
      \\ Cases_on`n' = n`
      >- (
        pop_assum SUBST_ALL_TAC
        \\ ntac 2 (pop_assum kall_tac)
        \\ Induct_on`n` \\ simp[]
        \\ simp[FUNPOW_SUC] )
      \\ pop_assum mp_tac
      \\ rpt(pop_assum kall_tac)
      \\ strip_tac
      \\ wlog_tac`n < n'`[`n`,`n'`]
      >- metis_tac[NOT_LESS, LESS_OR_EQ]
      \\ pop_assum mp_tac
      \\ pop_assum kall_tac
      \\ qid_spec_tac`n`
      \\ qid_spec_tac`n'`
      \\ Induct \\ simp[]
      \\ Cases \\ simp[]
      \\ simp[FUNPOW_SUC]
      \\ metis_tac[])
    \\ pop_assum strip_assume_tac
    \\ pop_assum kall_tac
    \\ simp[SURJ_DEF]
    \\ simp[IN_FOLDL_prod_env, PULL_EXISTS]
    \\ qx_gen_tac`s`
    \\ strip_tac >- fs[Abbr`ct`, cfT_def, cf0_def]
    \\ simp[]
    \\ qmatch_assum_rename_tac`e ∈ _.env`
    \\ qexists_tac`e`
    \\ conj_asm1_tac
    >- (
      pop_assum mp_tac
      \\ `MEM (EL n cs) cs` by metis_tac[MEM_EL]
      \\ pop_assum mp_tac
      \\ simp[Abbr`cs`, MEM_MAP, EL_MAP]
      \\ strip_tac \\ simp[]
      \\ simp[assume_def, cf_assume_def] )
    \\ SELECT_ELIM_TAC
    \\ `MEM (EL n cs) cs` by metis_tac[MEM_EL]
    \\ pop_assum mp_tac
    \\ simp[Abbr`cs`, MEM_MAP]
    \\ strip_tac \\ fs[]
    \\ conj_tac >- metis_tac[]
    \\ rpt strip_tac
    \\ `x' = y` by metis_tac[EXISTS_UNIQUE_ALT]
    \\ gvs[] \\ rfs[EL_MAP]
    \\ `fi x' = n` suffices_by rw[]
    \\ `x' = EL n (SET_TO_LIST x)` suffices_by metis_tac[]
    \\ metis_tac[MEM_EL, MEM_SET_TO_LIST])
  \\ simp[homotopy_equiv_def]
  \\ qexists_tac`mk_chu_morphism c (FOLDL prod ct cs) <|
       map_agent := λa. FUNPOW (λp. encode_pair (p, a)) (LENGTH cs) "";
       map_env := LINV ef c.env |>`
  \\ qpat_x_assum`∀f. _ ∧ _ ⇒ _`mp_tac
  \\ CONV_TAC(LAND_CONV(SIMP_CONV std_ss [GSYM RIGHT_EXISTS_IMP_THM]))
  \\ simp[SKOLEM_THM]
  \\ disch_then(qx_choose_then`fa`strip_assume_tac)
  \\ qexists_tac`mk_chu_morphism (FOLDL prod ct cs) c <|
       map_agent := λp. fa (restrict (λs.
         SND (decode_pair
           (FUNPOW (FST o decode_pair) (LENGTH cs - (fi s) - 1) p))) x);
       map_env := ef |>`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ conj_tac
    >- (
      irule FOLDL_prod_in_chu_objects
      \\ simp[Abbr`cs`, Abbr`ct`, EVERY_MAP] )
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ conj_tac >- metis_tac[BIJ_LINV_BIJ, BIJ_DEF, INJ_DEF]
    \\ conj_tac
    >- (
      simp[FOLDL_prod_agent]
      \\ simp[Abbr`ct`, cfT_def, cf0_def]
      \\ simp[Abbr`cs`, FOLDL_MAP]
      \\ simp[assume_def, cf_assume_def]
      \\ rpt (pop_assum kall_tac)
      \\ qspec_tac(`SET_TO_LIST x`,`ls`)
      \\ ho_match_mp_tac SNOC_INDUCT
      \\ simp[]
      \\ simp[FUNPOW_SUC, FOLDL_SNOC])
    \\ rpt strip_tac
    \\ qmatch_goalsub_abbrev_tac` _.eval aa f`
    \\ `∃e. e ∈ c.env ∧ f = ef e` by metis_tac[BIJ_DEF, SURJ_DEF]
    \\ `LINV ef c.env f = e` by metis_tac[LINV_DEF, BIJ_DEF]
    \\ pop_assum SUBST_ALL_TAC
    \\ pop_assum SUBST_ALL_TAC
    \\ simp[Abbr`ef`]
    \\ qmatch_goalsub_abbrev_tac`fi s`
    \\ `s ∈ x`
    by (
      simp[Abbr`s`]
      \\ SELECT_ELIM_TAC \\ simp[]
      \\ metis_tac[EXISTS_UNIQUE_ALT] )
    \\ `fi s < LENGTH cs`
    by metis_tac[BIJ_DEF, INJ_DEF, IN_COUNT]
    \\ qmatch_goalsub_abbrev_tac`FUNPOW _ n`
    \\ `n < LENGTH cs` by simp[Abbr`n`]
    \\ pop_assum mp_tac
    \\ simp[Abbr`aa`]
    \\ simp[Abbr`cs`]
    \\ qmatch_goalsub_abbrev_tac`n < LENGTH ls`
    \\ `e ∈ (assume (EL (LENGTH ls - n - 1) ls) c).env`
    by (
      gs[Abbr`n`]
      \\ first_x_assum(qspec_then`s`mp_tac)
      \\ simp[EL_MAP]
      \\ metis_tac[EXISTS_UNIQUE_ALT] )
    \\ pop_assum mp_tac
    \\ qpat_x_assum `c ∈ _`mp_tac
    \\ `"" ∈ ct.agent` by simp[Abbr`ct`, cfT_def, cf0_def]
    \\ pop_assum mp_tac
    \\ map_every qid_spec_tac[`a`,`e`,`n`,`ct`,`ls`]
    \\ rpt (pop_assum kall_tac)
    \\ ho_match_mp_tac SNOC_INDUCT
    \\ rewrite_tac[FOLDL_SNOC, MAP_SNOC]
    \\ rw[]
    \\ Cases_on`n` \\ fs[]
    >- (
      simp[prod_def, mk_cf_def, PULL_EXISTS, EXISTS_PROD, sum_eval_def, GSYM ADD1]
      \\ fs[EL_LENGTH_SNOC, FUNPOW_SUC]
      \\ simp[FOLDL_prod_agent]
      \\ simp[FOLDL_MAP]
      \\ gs[cf_assume_def, assume_def, mk_cf_def]
      \\ reverse(Cases_on`a ∈ c.agent`)
      >- metis_tac[in_chu_objects, wf_def]
      \\ rw[]
      \\ `F` suffices_by rw[]
      \\ pop_assum mp_tac \\ simp[]
      \\ qpat_x_assum`"" ∈ _`mp_tac
      \\ pop_assum mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ qid_spec_tac`ls`
      \\ ho_match_mp_tac SNOC_INDUCT
      \\ rw[FOLDL_SNOC, FUNPOW_SUC] )
    \\ simp[prod_def, mk_cf_def, PULL_EXISTS, EXISTS_PROD, sum_eval_def, GSYM ADD1]
    \\ fs[EL_LENGTH_SNOC, FUNPOW_SUC]
    \\ fs[ADD1]
    \\ fs[EL_SNOC]
    \\ reverse(Cases_on`a ∈ c.agent`)
    >- metis_tac[in_chu_objects, wf_def]
    \\ rw[]
    \\ `F` suffices_by rw[]
    \\ pop_assum mp_tac \\ simp[]
    \\ simp[IN_FOLDL_prod_env]
    \\ simp[assume_def, cf_assume_def]
    \\ reverse conj_tac
    >- (
      disj2_tac
      \\ qmatch_asmsub_abbrev_tac`EL m ls`
      \\ qexists_tac`m`
      \\ simp[EL_MAP, Abbr`m`]
      \\ metis_tac[] )
    \\ qpat_x_assum`"" ∈ _`mp_tac
    \\ pop_assum mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ qid_spec_tac`ls`
    \\ ho_match_mp_tac SNOC_INDUCT
    \\ rw[MAP_SNOC, FOLDL_SNOC, FUNPOW_SUC]
    \\ fs[prod_def, assume_def, cf_assume_def] )
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ conj_tac
    >- (
      irule FOLDL_prod_in_chu_objects
      \\ simp[Abbr`cs`, Abbr`ct`, EVERY_MAP] )
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[Once restrict_def]
    \\ conj_asm1_tac >- metis_tac[BIJ_DEF, INJ_DEF]
    \\ simp[Once restrict_def]
    \\ qho_match_abbrev_tac`(∀a. _ a ⇒ fa (f a) ∈ _) ∧ _`
    \\ simp[]
    \\ `∀p. p ∈ (FOLDL prod ct cs).agent ⇒
            extensional (f p) x ∧
            IMAGE (f p) x ⊆ c.agent`
    by (
      simp[Abbr`f`]
      \\ simp[SUBSET_DEF, PULL_EXISTS, restrict_def]
      \\ ntac 5 (pop_assum kall_tac)
      \\ gs[Abbr`cs`, Abbr`ct`]
      \\ pop_assum mp_tac
      \\ `∀s. s ∈ x ⇔ MEM s (SET_TO_LIST x)` by simp[]
      \\ pop_assum (fn th => rewrite_tac[th])
      \\ qspec_tac(`SET_TO_LIST x`,`ls`)
      \\ ntac 4 (pop_assum kall_tac)
      \\ ho_match_mp_tac SNOC_INDUCT
      \\ simp[MAP_SNOC, FOLDL_SNOC]
      \\ ntac 5 strip_tac
      \\ simp[prod_def, EXISTS_PROD, PULL_EXISTS]
      \\ simp[assume_def, cf_assume_def]
      \\ ntac 5 strip_tac
      >- (
        first_x_assum(qspec_then`LENGTH ls`mp_tac)
        \\ simp[EL_LENGTH_SNOC, ADD1] )
      \\ pop_assum mp_tac
      \\ simp[ADD1]
      \\ qmatch_goalsub_rename_tac`fi s`
      \\ strip_tac
      \\ `∃n. (n < LENGTH ls) ∧ s = EL n ls` by metis_tac[MEM_EL]
      \\ `∀n. (n < LENGTH ls) ⇒ fi (EL n ls) = n`
      by (
        qx_gen_tac`m` \\ strip_tac
        \\ first_x_assum(qspec_then`m`mp_tac)
        \\ simp[EL_SNOC] )
      \\ fs[]
      \\ Cases_on`LENGTH ls - n` \\ fs[]
      \\ simp[FUNPOW]
      \\ first_x_assum drule
      \\ disch_then drule \\ simp[]
      \\ qmatch_assum_rename_tac`LENGTH ls - n = SUC m`
      \\ `LENGTH ls - (n + 1) = m` by simp[]
      \\ pop_assum SUBST_ALL_TAC
      \\ simp[] )
    \\ conj_tac >- metis_tac[]
    \\ simp[restrict_def]
    \\ qx_genl_tac[`p`,`e`]
    \\ strip_tac
    \\ first_x_assum drule
    \\ disch_then assume_tac
    \\ first_x_assum(qspec_then`f p`mp_tac)
    \\ impl_tac >- first_assum ACCEPT_TAC
    \\ strip_tac
    \\ first_x_assum drule
    \\ disch_then (SUBST_ALL_TAC o SYM)
    \\ simp[Abbr`ef`]
    \\ qmatch_goalsub_abbrev_tac`f p s`
    \\ simp[assume_def, cf_assume_def]
    \\ qmatch_goalsub_abbrev_tac`fi s'`
    \\ `s ∈ x`
    by (
      simp[Abbr`s`]
      \\ SELECT_ELIM_TAC
      \\ simp[]
      \\ metis_tac[in_chu_objects, wf_def, partitions_thm] )
    \\ `s' = s`
    by (
      simp[Abbr`s`, Abbr`s'`]
      \\ last_x_assum(qspec_then`e`mp_tac)
      \\ simp[assume_def, cf_assume_def]
      \\ simp[EXISTS_UNIQUE_THM]
      \\ strip_tac
      \\ SELECT_ELIM_TAC
      \\ conj_tac >- metis_tac[]
      \\ rpt strip_tac
      \\ SELECT_ELIM_TAC
      \\ conj_tac >- metis_tac[]
      \\ rpt strip_tac
      \\ qhdtm_x_assum`partitions`mp_tac
      \\ simp[partitions_thm, EXISTS_UNIQUE_ALT]
      \\ metis_tac[wf_def, in_chu_objects] )
    \\ `∀a. a ∈ c.agent ⇒ c.eval a e ∈ s`
    by (
      fs[Abbr`s`, Abbr`s'`]
      \\ qpat_x_assum`_ = _`(SUBST1_TAC o SYM)
      \\ last_x_assum(qspec_then`e`mp_tac)
      \\ simp[assume_def, cf_assume_def]
      \\ simp[EXISTS_UNIQUE_THM]
      \\ metis_tac[])
    \\ first_assum SUBST1_TAC
    \\ pop_assum mp_tac
    \\ simp[Abbr`f`, restrict_def]
    \\ qpat_x_assum`p ∈ _`mp_tac
    \\ simp[Abbr`cs`]
    \\ qpat_x_assum`∀s. _ ⇒ fi _ = _`mp_tac
    \\ simp[]
    \\ qpat_x_assum`e ∈ _`mp_tac
    \\ `MEM s (SET_TO_LIST x)` by simp[]
    \\ pop_assum mp_tac
    \\ ntac 22 (pop_assum kall_tac)
    \\ qid_spec_tac`s`
    \\ qid_spec_tac`p`
    \\ qspec_tac(`SET_TO_LIST x`,`ls`)
    \\ ho_match_mp_tac SNOC_INDUCT
    \\ rewrite_tac[MAP_SNOC, FOLDL_SNOC]
    \\ simp[]
    \\ rpt strip_tac
    >- (
      first_x_assum(qspec_then`LENGTH ls`mp_tac)
      \\ simp[EL_LENGTH_SNOC]
      \\ strip_tac
      \\ qpat_x_assum`p ∈ _`mp_tac
      \\ simp[prod_def, PULL_EXISTS, EXISTS_PROD, mk_cf_def]
      \\ simp[sum_eval_def]
      \\ simp[assume_def, cf_assume_def, mk_cf_def]
      \\ rw[] )
    \\ `∃n. (n < LENGTH ls) ∧ s = EL n ls` by metis_tac[MEM_EL]
    \\ `∀n. (n < LENGTH ls) ⇒ fi (EL n ls) = n`
    by (
      qx_gen_tac`m` \\ strip_tac
      \\ first_x_assum(qspec_then`m`mp_tac)
      \\ simp[EL_SNOC] )
    \\ fs[]
    \\ qpat_x_assum`p ∈ _`mp_tac
    \\ simp[prod_def, mk_cf_def, PULL_EXISTS, EXISTS_PROD]
    \\ ntac 3 strip_tac
    \\ Cases_on`LENGTH ls - n` \\ fs[]
    \\ simp[Once FUNPOW_SUC]
    \\ simp[Once FUNPOW_SUC]
    \\ simp[Once FUNPOW_SUC]
    \\ simp[Once FUNPOW]
    \\ simp[sum_eval_def]
    \\ simp[IN_FOLDL_prod_env]
    \\ qmatch_assum_rename_tac`LENGTH ls - n = SUC m`
    \\ `LENGTH ls - (n + 1) = m` by simp[]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[]
      \\ disj2_tac
      \\ qexists_tac`n`
      \\ simp[EL_MAP]
      \\ simp[assume_def, cf_assume_def]
      \\ metis_tac[] )
    \\ pop_assum kall_tac
    \\ first_x_assum drule
    \\ disch_then drule \\ simp[])
  \\ qmatch_goalsub_abbrev_tac`homotopic _ (j o k -: _)`
  \\ qpat_assum`k :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`j :- _ → _ -: _` o mp_then Any strip_assume_tac)
  \\ qpat_assum`j :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`k :- _ → _ -: _` o mp_then Any strip_assume_tac)
  \\ `EVERY (λc. c ∈ chu_objects w) cs`
  by simp[Abbr`cs`, EVERY_MAP]
  \\ `ct ∈ chu_objects w` by simp[Abbr`ct`]
  \\ simp[homotopic_id_map_env_id]
  \\ simp[restrict_def]
  \\ simp[Abbr`k`, Abbr`j`, mk_chu_morphism_def]
  \\ simp[restrict_def]
  \\ metis_tac[BIJ_LINV_BIJ, BIJ_LINV_THM, BIJ_DEF, INJ_DEF]
QED

Theorem obs_part_assuming:
  c ∈ chu_objects w ∧ w ≠ ∅ ⇒
  obs_part c = obs_part_assuming c
Proof
  metis_tac[obs_part_imp_assuming,
            obs_part_assuming_imp_additive,
            obs_part_additive_imp,
            SET_EQ_SUBSET, SUBSET_TRANS]
QED

Theorem obs_part_additive:
  c ∈ chu_objects w ∧ w ≠ ∅ ⇒
  obs_part c = obs_part_additive c
Proof
  metis_tac[obs_part_imp_assuming,
            obs_part_assuming_imp_additive,
            obs_part_additive_imp,
            SET_EQ_SUBSET, SUBSET_TRANS]
QED

(* TODO: additive definitions example *)

Definition powerless_outside_def:
  powerless_outside c s ⇔
    ∀a e. a ∈ c.agent ∧ e ∈ c.env ∧ c.eval a e ∉ s ⇒
      ∀a'. a' ∈ c.agent ⇒ c.eval a' e = c.eval a e
End

Theorem powerless_outside_superset:
  powerless_outside c s ∧ s ⊆ t ⇒
  powerless_outside c t
Proof
  rw[powerless_outside_def, SUBSET_DEF]
  \\ metis_tac[]
QED

Theorem powerless_outside_tensor:
  powerless_outside c s ∧ powerless_outside d s ⇒
  powerless_outside (tensor c d) s
Proof
  rw[powerless_outside_def, tensor_def, PULL_EXISTS, EXISTS_PROD, mk_cf_def]
  \\ gs[hom_def]
  \\ reverse IF_CASES_TAC >- metis_tac[]
  \\ qmatch_assum_abbrev_tac`b` \\ gs[]
  \\ qpat_x_assum`_ ∉ _`mp_tac
  \\ DEP_REWRITE_TAC[Q.GEN`w`decode_encode_chu_morphism]
  \\ conj_tac >- metis_tac[] \\ strip_tac
  \\ qpat_x_assum`b`kall_tac \\ qunabbrev_tac`b`
  \\ qmatch_goalsub_rename_tac`c.eval a (m.map.map_env e) = c.eval b (_ f)`
  \\ irule EQ_TRANS
  \\ qexists_tac`c.eval a (m.map.map_env f)`
  \\ reverse conj_tac
  >- (
    first_x_assum irule \\ simp[]
    \\ fs[maps_to_in_chu, is_chu_morphism_def] )
  \\ fs[maps_to_in_chu, is_chu_morphism_def]
  \\ first_x_assum irule \\ simp[]
  \\ metis_tac[]
QED

Theorem powerless_outside_FOLDL_tensor:
  EVERY (flip powerless_outside s) (c::ls) ⇒
  powerless_outside (FOLDL tensor c ls) s
Proof
  qid_spec_tac`ls`
  \\ ho_match_mp_tac SNOC_INDUCT
  \\ rw[FOLDL_SNOC]
  \\ irule powerless_outside_tensor
  \\ fs[EVERY_SNOC]
QED

Theorem powerless_outside_cf1[simp]:
  powerless_outside (cf1 x y) z
Proof
  rw[powerless_outside_def]
QED

Definition obs_part_multiplicative_def:
  obs_part_multiplicative c = { v |
    let w = c.world in
      partitions v w ∧
      ∃cs.
        LIST_REL (λc s. c ∈ chu_objects w ∧ powerless_outside c s)
          cs (SET_TO_LIST v) ∧
        c ≃ FOLDL tensor (cf1 w w) cs -: w }
End

Definition obs_part_mult_constructive_def:
  obs_part_mult_constructive c = { v |
    let w = c.world in
      partitions v w ∧
      c ≃ FOLDL tensor (cf1 w w)
        (MAP (λs. assume s c && cf1 w ((w DIFF s) INTER image c))
             (SET_TO_LIST v)) -: w }
End

Theorem obs_part_mult_constructive_imp_multiplicative:
  obs_part_mult_constructive c ⊆ obs_part_multiplicative c
Proof
  simp[SUBSET_DEF, obs_part_multiplicative_def, obs_part_mult_constructive_def]
  \\ rpt strip_tac
  \\ `c ∈ chu_objects c.world` by imp_res_tac homotopy_equiv_in_chu_objects
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ simp[LIST_REL_MAP1]
  \\ irule EVERY2_refl
  \\ imp_res_tac in_chu_objects
  \\ imp_res_tac in_chu_objects_finite_world
  \\ fs[]
  \\ drule partitions_FINITE
  \\ simp[] \\ strip_tac
  \\ qx_gen_tac`s` \\ strip_tac
  \\ conj_asm1_tac
  >- (
    irule prod_in_chu_objects \\ simp[]
    \\ irule cf1_in_chu_objects
    \\ simp[SUBSET_DEF] )
  \\ simp[powerless_outside_def]
  \\ simp[prod_def, PULL_EXISTS, EXISTS_PROD, mk_cf_def]
  \\ rpt gen_tac \\ strip_tac \\ gs[sum_eval_def]
  \\ gs[assume_def, cf_assume_def, mk_cf_def]
QED

Theorem homotopy_equiv_obs_part_additive:
  c1 ≃ c2 -: w ⇒ obs_part_additive c1 = obs_part_additive c2
Proof
  `∀c1 c2. c1 ≃ c2 -: w ⇒ obs_part_additive c1  ⊆ obs_part_additive c2`
  suffices_by metis_tac[SET_EQ_SUBSET, homotopy_equiv_sym]
  \\ rpt strip_tac
  \\ imp_res_tac homotopy_equiv_in_chu_objects
  \\ imp_res_tac in_chu_objects
  \\ simp[obs_part_additive_def, SUBSET_DEF, PULL_EXISTS]
  \\ qx_genl_tac[`v`,`f`] \\ strip_tac
  \\ metis_tac[homotopy_equiv_trans, homotopy_equiv_sym]
QED

Theorem homotopy_equiv_obs_part:
  w ≠ ∅ ∧ c1 ≃ c2 -: w ⇒ obs_part c1 = obs_part c2
Proof
  strip_tac
  \\ imp_res_tac homotopy_equiv_in_chu_objects
  \\ imp_res_tac obs_part_additive
  \\ metis_tac[homotopy_equiv_obs_part_additive]
QED

Theorem obs_part_multiplicative_imp:
  obs_part_multiplicative c ⊆ obs_part c
Proof
  rw[SUBSET_DEF, obs_part_multiplicative_def]
  \\ qmatch_assum_abbrev_tac`c ≃ d -: w`
  \\ Cases_on`w = ∅`
  >- (
    fs[partitions_thm]
    \\ `x = ∅` by metis_tac[MEMBER_NOT_EMPTY]
    \\ simp[obs_part_def, partitions_thm] )
  \\ `x ∈ obs_part d` suffices_by metis_tac[homotopy_equiv_obs_part]
  \\ imp_res_tac homotopy_equiv_in_chu_objects
  \\ imp_res_tac in_chu_objects_finite_world
  \\ imp_res_tac partitions_FINITE
  \\ imp_res_tac in_chu_objects
  \\ simp[obs_part_def]
  \\ rpt strip_tac
  \\ `MEM s (SET_TO_LIST x)` by simp[]
  \\ fs[MEM_EL]
  \\ qmatch_assum_abbrev_tac`n < LENGTH ss`
  \\ qabbrev_tac `tf = λi. if i = n then LENGTH ss - 1
                           else if i = LENGTH ss - 1 then n
                           else i`
  \\ `tf PERMUTES (count (LENGTH ss))`
  by (
    simp[BIJ_IFF_INV]
    \\ conj_tac >- simp[Abbr`tf`]
    \\ qexists_tac`tf` \\ simp[Abbr`tf`] )
  \\ `PERM ss (GENLIST (λi. EL (tf i) ss) (LENGTH ss))`
  by metis_tac[PERM_BIJ_IFF]
  \\ `LENGTH cs = LENGTH ss` by metis_tac[LIST_REL_LENGTH]
  \\ `PERM cs (GENLIST (λi. EL (tf i) cs) (LENGTH cs))`
  by metis_tac[PERM_BIJ_IFF]
  \\ qmatch_assum_abbrev_tac`LIST_REL P cs ss`
  \\ qmatch_assum_abbrev_tac`PERM ss ss0`
  \\ qmatch_assum_abbrev_tac`PERM cs cc0`
  \\ `LIST_REL P cc0 ss0`
  by (
    simp[Abbr`cc0`,Abbr`ss0`,LIST_REL_GENLIST]
    \\ metis_tac[LIST_REL_EL_EQN, BIJ_DEF, INJ_DEF, IN_COUNT] )
  \\ `d ≅ FOLDL tensor (cf1 w w) cc0 -: chu w`
  by (
    simp[Abbr`d`]
    \\ irule FOLDL_PERM_iso
    \\ simp[EVERY_MEM]
    \\ rpt strip_tac
    \\ imp_res_tac LIST_REL_MEM_IMP
    \\ fs[Abbr`P`] )
  \\ qmatch_assum_abbrev_tac`d ≅ d0 -: _`
  \\ `LAST ss0 ∈ obs d0` suffices_by (
    Cases_on `ss0 = []` >- fs[]
    \\ simp[Abbr`ss0`, LAST_EL]
    \\ `tf (PRE (LENGTH ss)) = n` by rw[Abbr`tf`]
    \\ metis_tac[obs_homotopy_equiv, iso_homotopy_equiv] )
  \\ `∃c0 cr s0 sr. cc0 = SNOC c0 cr ∧ ss0 = SNOC s0 sr`
  by (metis_tac[SNOC_CASES, LENGTH, prim_recTheory.NOT_LESS_0, PERM_LENGTH])
  \\ ntac 2 BasicProvers.VAR_EQ_TAC
  \\ fs[FOLDL_SNOC, Excl"SNOC_APPEND"]
  \\ qmatch_asmsub_abbrev_tac`d0 = tensor d1 c0`
  \\ `d1 ∈ chu_objects w ∧ c0 ∈ chu_objects w`
  by (
    fs[LIST_REL_SNOC, Abbr`P`]
    \\ simp[Abbr`d1`]
    \\ irule FOLDL_tensor_in_chu_objects
    \\ simp[EVERY_MEM]
    \\ rpt strip_tac
    \\ imp_res_tac LIST_REL_MEM_IMP
    \\ fs[] )
  \\ `s0 ∈ obs (tensor c0 d1)` suffices_by
    metis_tac[tensor_comm, obs_homotopy_equiv, iso_homotopy_equiv]
  \\ `MEM s0 ss` by metis_tac[MEM_SNOC, MEM_PERM]
  \\ `powerless_outside d1 (w DIFF s0)`
  by (
    simp[Abbr`d1`]
    \\ irule powerless_outside_FOLDL_tensor
    \\ simp[EVERY_MEM]
    \\ simp[MEM_EL, PULL_EXISTS]
    \\ fs[LIST_REL_EL_EQN]
    \\ qx_gen_tac`m` \\ strip_tac
    \\ first_x_assum(qspec_then`m`mp_tac)
    \\ simp[EL_SNOC, Abbr`P`] \\ strip_tac
    \\ irule powerless_outside_superset
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ `MEM (EL m sr) ss ∧ EL m sr ≠ s0`
    by (
      `MEM (EL m sr) sr` by metis_tac[MEM_EL]
      \\ `MEM (EL m sr) (SNOC s0 sr)` by metis_tac[MEM_SNOC]
      \\ conj_asm1_tac >- metis_tac[MEM_PERM]
      \\ `ALL_DISTINCT ss` by metis_tac[ALL_DISTINCT_SET_TO_LIST]
      \\ `ALL_DISTINCT (SNOC s0 sr)` by metis_tac[ALL_DISTINCT_PERM]
      \\ metis_tac[ALL_DISTINCT_SNOC] )
    \\ rfs[Abbr`ss`]
    \\ fs[partitions_thm]
    \\ simp[SUBSET_DEF]
    \\ ntac 2 strip_tac
    \\ conj_tac >- metis_tac[SUBSET_DEF]
    \\ PROVE_TAC[SUBSET_DEF, EXISTS_UNIQUE_ALT])
  \\ `powerless_outside c0 s0` by fs[LIST_REL_SNOC, Abbr`P`]
  \\ imp_res_tac in_chu_objects
  \\ simp[obs_def]
  \\ simp[Ntimes tensor_def 3, PULL_EXISTS, EXISTS_PROD]
  \\ conj_asm1_tac
  >- ( rfs[Abbr`ss`] \\ metis_tac[partitions_thm] )
  \\ qx_genl_tac[`a1`,`b1`,`a2`,`b2`]
  \\ strip_tac
  \\ simp[ifs_def]
  \\ qexists_tac`encode_pair (a1,b2)`
  \\ simp[Once tensor_def, PULL_EXISTS]
  \\ simp[Once tensor_def, PULL_EXISTS, hom_def]
  \\ gen_tac \\ strip_tac
  \\ simp[tensor_def, mk_cf_def, hom_def]
  \\ reverse IF_CASES_TAC >- metis_tac[]
  \\ pop_assum kall_tac \\ simp[]
  \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
  \\ simp[]
  \\ fs[maps_to_in_chu, is_chu_morphism_def]
  \\ fs[powerless_outside_def]
  \\ metis_tac[]
QED

Theorem obs_part_assuming_imp_mult_constructive:
  obs_part_assuming c ⊆ obs_part_mult_constructive c
Proof
  simp[SUBSET_DEF]
  \\ qx_gen_tac`v` \\ strip_tac
  \\ `v ∈ obs_part c` by metis_tac[obs_part_assuming_imp_additive, obs_part_additive_imp, SUBSET_DEF]
  \\ fs[obs_part_assuming_def, obs_part_mult_constructive_def]
  \\ qmatch_assum_abbrev_tac`partitions v w`
  \\ irule homotopy_equiv_trans
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ `c ∈ chu_objects w` by imp_res_tac homotopy_equiv_in_chu_objects
  \\ qmatch_goalsub_abbrev_tac`MAP _ ls`
  \\ `ALL_DISTINCT ls ∧ ∀x. MEM x ls ⇔ x ∈ v` by (
    imp_res_tac in_chu_objects_finite_world
    \\ imp_res_tac partitions_FINITE
    \\ simp[Abbr`ls`])
  \\ qpat_x_assum`c ≃ _ -: _`kall_tac
  \\ Cases_on`w = ∅`
  >- (
    imp_res_tac partitions_FINITE
    \\ fs[partitions_thm, EXISTS_UNIQUE_ALT]
    \\ `v = ∅` by metis_tac[MEMBER_NOT_EMPTY, MEM_SET_TO_LIST, MEM]
    \\ fs[Abbr`ls`]
    \\ `cfT w = cf1 w w` suffices_by simp[]
    \\ simp[cfT_def, cf0_def, cf1_def, cf_component_equality,
            mk_cf_def, swap_def, FUN_EQ_THM])
  \\ ntac 3 (pop_assum mp_tac)
  \\ rpt(qhdtm_x_assum`Abbrev`kall_tac)
  \\ ntac 3 (pop_assum mp_tac)
  \\ qid_spec_tac`v`
  \\ Induct_on`LENGTH ls`
  >- (
    rw[]
    \\ `v = ∅` by metis_tac[MEMBER_NOT_EMPTY, MEM_SET_TO_LIST, MEM]
    \\ fs[partitions_thm, EXISTS_UNIQUE_ALT]
    \\ metis_tac[MEMBER_NOT_EMPTY])
  \\ qmatch_goalsub_rename_tac`SUC n`
  \\ rpt strip_tac
  \\ qspec_then`ls`FULL_STRUCT_CASES_TAC SNOC_CASES
  >- gs[]
  \\ qmatch_asmsub_rename_tac`SNOC s1 ls`
  \\ qspec_then`ls`FULL_STRUCT_CASES_TAC SNOC_CASES
  >- (
    gs[]
    \\ irule homotopy_equiv_trans
    \\ `assume s1 c ∈ chu_objects w` by simp[]
    \\ `s1 = w` by (
      fs[partitions_thm, EXISTS_UNIQUE_ALT]
      \\ metis_tac[MEMBER_NOT_EMPTY, SUBSET_DEF, EXTENSION] )
    \\ pop_assum SUBST_ALL_TAC
    \\ simp[cf1_empty]
    \\ imp_res_tac in_chu_objects_finite_world
    \\ `cfT w ∈ chu_objects w` by simp[]
    \\ `cf1 w w ∈ chu_objects w` by simp[]
    \\ metis_tac[tensor_cf1, prod_cfT, homotopy_equiv_trans,
                 homotopy_equiv_sym, iso_homotopy_equiv,
                 tensor_in_chu_objects, prod_in_chu_objects])
  \\ qmatch_asmsub_rename_tac`SNOC s1 (SNOC s2 ls)`
  \\ `s1 ∪ s2 INSERT v DELETE s1 DELETE s2 ∈ obs_part c`
  by (
    fs[obs_part_def]
    \\ imp_res_tac in_chu_objects \\ fs[]
    \\ reverse conj_tac >- metis_tac[obs_union]
    \\ fs[partitions_thm]
    \\ conj_tac >- (
      fs[SUBSET_DEF] \\ metis_tac[IN_UNION, EMPTY_UNION] )
    \\ rpt strip_tac
    \\ `∃!s. s ∈ v ∧ y ∈ s` by PROVE_TAC[]
    \\ fs[EXISTS_UNIQUE_ALT]
    \\ Cases_on`s = s1`
    >- (
      qexists_tac`s1 ∪ s2`
      \\ rw[EQ_IMP_THM] \\ rw[]
      \\ metis_tac[] )
    \\ Cases_on`s = s2`
    >- (
      qexists_tac`s1 ∪ s2`
      \\ rw[EQ_IMP_THM] \\ rw[]
      \\ metis_tac[] )
    \\ qexists_tac`s`
    \\ rw[EQ_IMP_THM] \\ gs[]
    \\ metis_tac[])
  \\ qmatch_assum_abbrev_tac`v1 ∈ obs_part _`
  \\ first_x_assum(qspec_then`SNOC (s1 ∪ s2) ls`mp_tac)
  \\ impl_tac >- fs[LENGTH_SNOC]
  \\ disch_then(qspec_then`v1`mp_tac)
  \\ impl_tac >- gs[obs_part_def, in_chu_objects]
  \\ simp[]
  \\ impl_keep_tac
  >- (
    fs[ALL_DISTINCT_SNOC]
    \\ strip_tac
    \\ `s1 ∈ v ∧ s1 ∪ s2 ∈ v` by metis_tac[]
    \\ `s1 ≠ ∅ ∧ s2 ≠ ∅` by metis_tac[partitions_thm]
    \\ `s1 ≠ s1 ∪ s2` by metis_tac[SUBSET_UNION_ABSORPTION, SUBSET_REFL]
    \\ `DISJOINT s1 (s1 ∪ s2)` by metis_tac[partitions_DISJOINT]
    \\ metis_tac[IN_DISJOINT, IN_UNION, MEMBER_NOT_EMPTY] )
  \\ impl_tac
  >- ( fs[ALL_DISTINCT_SNOC, Abbr`v1`] \\ metis_tac[] )
  \\ simp[MAP_SNOC, FOLDL_SNOC]
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`cr && _ && _`
  \\ qmatch_goalsub_abbrev_tac`tensor (tensor tr p2) p1`
  \\ qmatch_asmsub_abbrev_tac`tensor tr p12`
  \\ imp_res_tac in_chu_objects_finite_world
  \\ drule partitions_FINITE
  \\ simp[] \\ strip_tac
  \\ `v ∈ obs_part_assuming c ∧ v1 ∈ obs_part_assuming c`
  by metis_tac[obs_part_assuming]
  \\ fs[obs_part_assuming_def]
  \\ qmatch_assum_abbrev_tac`c ≃ cr2 -: _`
  \\ qpat_x_assum`c ≃ cr2 -: _`mp_tac
  \\ qmatch_assum_abbrev_tac`c ≃ cr1 -: _`
  \\ strip_tac
  \\ `c.world = w` by metis_tac[in_chu_objects] \\ fs[]
  \\ irule homotopy_equiv_trans
  \\ qexists_tac`cr && assume (s1 ∪ s2) c`
  \\ `cr1 ≃ cr2 -: w` by metis_tac[homotopy_equiv_trans, homotopy_equiv_sym]
  \\ qmatch_asmsub_abbrev_tac`FOLDL prod ct (MAP f _)`
  \\ `cr && assume s2 c && assume s1 c =
      FOLDL prod ct (MAP f (SNOC s1 (SNOC s2 ls)))`
  by ( simp[MAP_SNOC, FOLDL_SNOC, Abbr`f`] )
  \\ `cr && assume (s1 ∪ s2) c =
      FOLDL prod ct (MAP f (SNOC (s1 ∪ s2) ls))`
  by ( simp_tac(srw_ss())[MAP_SNOC, FOLDL_SNOC, Abbr`f`] \\ simp[])
  \\ `ct ∈ chu_objects w` by simp[Abbr`ct`]
  \\ `tr ∈ chu_objects w`
  by (
    simp[Abbr`tr`]
    \\ irule FOLDL_tensor_in_chu_objects
    \\ rw[EVERY_MAP, EVERY_MEM]
    \\ irule prod_in_chu_objects \\ simp[]
    \\ irule cf1_in_chu_objects
    \\ simp[SUBSET_DEF] )
  \\ conj_tac
  >- (
    irule homotopy_equiv_trans
    \\ qexists_tac`cr1`
    \\ conj_tac
    >- (
      simp[Abbr`cr1`]
      \\ irule FOLDL_PERM_equiv
      \\ simp[Abbr`f`, EVERY_MAP]
      \\ irule PERM_MAP
      \\ irule PERM_ALL_DISTINCT
      \\ simp[] )
    \\ irule homotopy_equiv_trans
    \\ qexists_tac`cr2`
    \\ simp[Abbr`cr2`]
    \\ irule FOLDL_PERM_equiv
    \\ simp[Abbr`f`, EVERY_MAP]
    \\ irule PERM_MAP
    \\ irule PERM_ALL_DISTINCT
    \\ `FINITE v1` by simp[Abbr`v1`]
    \\ simp[]
    \\ simp[Abbr`v1`]
    \\ fs[ALL_DISTINCT_SNOC]
    \\ metis_tac[])
  \\ irule homotopy_equiv_trans
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ irule homotopy_equiv_trans
  \\ qexists_tac`tensor tr (tensor p2 p1)`
  \\ reverse conj_tac
  >- (
    irule iso_homotopy_equiv
    \\ irule tensor_assoc
    \\ simp[Abbr`p1`,Abbr`p2`]
    \\ conj_tac
    \\ irule prod_in_chu_objects \\ simp[]
    \\ irule cf1_in_chu_objects
    \\ simp[SUBSET_DEF] )
  \\ irule homotopy_equiv_tensor
  \\ simp[Abbr`p12`,Abbr`p1`,Abbr`p2`]
  \\ qmatch_goalsub_abbrev_tac`_ && c12`
  \\ qmatch_goalsub_abbrev_tac`tensor (_ && c2) (_ && c1)`
  \\ cheat
QED

val _ = export_theory();
