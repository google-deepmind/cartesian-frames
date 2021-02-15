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
  cf0Theory cf1Theory cf2Theory cf4Theory cf5Theory cf6Theory

val _ = new_theory"ex6";

Definition guests_def:
  guests = {"J";"K";"L"}
End

Theorem FINITE_guests[simp]:
  FINITE guests
Proof
  rw[guests_def]
QED

Definition party_world_def:
  party_world = IMAGE encode_set (POW guests)
End

Theorem FINITE_party_world[simp]:
  FINITE party_world
Proof
  rw[party_world_def]
QED

Definition guest_def:
  guest x = mk_cf <| world := party_world;
    agent := IMAGE encode_set (POW {x});
    env := IMAGE encode_set (POW (guests DELETE x));
    eval := λa e. encode_set (decode_set a ∪ decode_set e) |>
End

Definition jack_def:
  jack = guest "J"
End

Definition kate_def:
  kate = guest "K"
End

Definition luke_def:
  luke = guest "L"
End

Theorem guest_in_chu_objects[simp]:
  x ∈ guests ⇒
  guest x ∈ chu_objects party_world
Proof
  rw[guest_def, in_chu_objects, finite_cf_def]
  \\ rw[image_def, SUBSET_DEF]
  \\ DEP_REWRITE_TAC[decode_encode_set]
  \\ fs[IN_POW]
  \\ conj_tac >- metis_tac[SUBSET_FINITE, FINITE_DELETE, FINITE_SING, FINITE_guests]
  \\ simp[party_world_def]
  \\ qmatch_goalsub_abbrev_tac`encode_set s`
  \\ qexists_tac`s` \\ simp[Abbr`s`, IN_POW]
  \\ fs[SUBSET_DEF]
QED

Theorem guest_world[simp]:
  (guest x).world = party_world
Proof
  rw[guest_def]
QED

Theorem guest_eval:
  (guest x).eval a e =
  if a ∈ (guest x).agent ∧ e ∈ (guest x).env then
    encode_set (decode_set a ∪ decode_set e)
  else ARB
Proof
  rw[guest_def, mk_cf_def]
QED

Definition mor1_def:
  mor1 x y = mk_chu_morphism (guest x) (swap (guest y))
    <| map_agent := λa. if a = encode_set ∅ then a else encode_set {x};
       map_env := λe. if e = encode_set ∅ then e else encode_set {y} |>
End

Definition mor2_def:
  mor2 x y = mk_chu_morphism (guest x) (swap (guest y))
    <| map_agent := λa. if a = encode_set ∅
                            then encode_set (guests DIFF {x; y})
                            else encode_set (guests DIFF {y});
        map_env := λe. if e = encode_set ∅
                          then encode_set (guests DIFF {x; y})
                          else encode_set (guests DIFF {x}) |>
End

Theorem mor1_dom_cod[simp]:
  (mor1 x y).dom = guest x ∧
  (mor1 x y).cod = swap(guest y)
Proof
  rw[mor1_def]
QED

Theorem mor2_dom_cod[simp]:
  (mor2 x y).dom = guest x ∧
  (mor2 x y).cod = swap(guest y)
Proof
  rw[mor2_def]
QED

Theorem mor1_maps_to:
  x ∈ guests ∧ y ∈ guests ∧ x ≠ y ⇒
  mor1 x y :- guest x → swap (guest y) -: chu party_world
Proof
  rw[maps_to_in_chu, mor1_def]
  \\ simp[mk_chu_morphism_def, is_chu_morphism_def]
  \\ simp[restrict_def]
  \\ simp[guest_def, PULL_EXISTS]
  \\ simp[mk_cf_def]
  \\ dsimp[POW_EQNS]
  \\ qexistsl_tac[`{y}`,`{}`,`{x}`,`{}`]
  \\ simp[]
  \\ conj_asm1_tac >- simp[IN_POW]
  \\ conj_asm1_tac >- simp[IN_POW]
  \\ reverse IF_CASES_TAC >- metis_tac[]
  \\ reverse IF_CASES_TAC >- metis_tac[]
  \\ reverse IF_CASES_TAC >- metis_tac[IN_POW, EMPTY_SUBSET]
  \\ reverse IF_CASES_TAC >- metis_tac[IN_POW, EMPTY_SUBSET]
  \\ simp[UNION_COMM]
QED

Theorem mor2_maps_to:
  x ∈ guests ∧ y ∈ guests ∧ x ≠ y ⇒
  mor2 x y :- guest x → swap (guest y) -: chu party_world
Proof
  rw[maps_to_in_chu, mor2_def]
  \\ simp[mk_chu_morphism_def, is_chu_morphism_def]
  \\ simp[restrict_def]
  \\ simp[guest_def, PULL_EXISTS]
  \\ simp[mk_cf_def]
  \\ dsimp[POW_EQNS]
  \\ qexistsl_tac[`guests DIFF {x}`,`guests DIFF {x;y}`,
                  `guests DIFF {y}`,`guests DIFF {x;y}`]
  \\ simp[]
  \\ conj_asm1_tac >- simp[IN_POW, SUBSET_DEF]
  \\ conj_asm1_tac >- simp[IN_POW, SUBSET_DEF]
  \\ reverse IF_CASES_TAC >- metis_tac[]
  \\ reverse IF_CASES_TAC >- metis_tac[]
  \\ reverse IF_CASES_TAC >- metis_tac[]
  \\ reverse IF_CASES_TAC >- metis_tac[]
  \\ simp[]
  \\ simp[Once EXTENSION, GSYM CONJ_ASSOC]
  \\ conj_tac >- metis_tac[]
  \\ simp[Once EXTENSION]
  \\ conj_tac >- metis_tac[]
  \\ simp[Once EXTENSION]
  \\ metis_tac[]
QED

Theorem maps_to_swap_guest:
  x ∈ guests ∧ y ∈ guests ∧ x ≠ y ⇒
  (m :- guest x → swap (guest y) -: chu party_world ⇔
   m ∈ {mor1 x y; mor2 x y})
Proof
  strip_tac
  \\ simp[]
  \\ reverse eq_tac >- metis_tac[mor1_maps_to, mor2_maps_to]
  \\ simp[maps_to_in_chu]
  \\ simp[is_chu_morphism_def]
  \\ strip_tac
  \\ simp[morphism_component_equality]
  \\ fs[guest_def, PULL_EXISTS]
  \\ ntac 2 (pop_assum kall_tac)
  \\ fs[mk_cf_def]
  \\ fs[POW_EQNS]
  \\ pop_assum mp_tac \\ dsimp[]
  \\ ntac 2 (pop_assum mp_tac) \\ dsimp[]
  \\ rpt gen_tac
  \\ ntac 2 strip_tac
  \\ DEP_REWRITE_TAC[decode_encode_set]
  \\ fs[IN_POW]
  \\ conj_asm1_tac
  >- metis_tac [IN_POW, SUBSET_FINITE, FINITE_DELETE, FINITE_guests]
  \\ simp[]
  \\ strip_tac
  \\ rpt BasicProvers.VAR_EQ_TAC \\ fs[]
  \\ fs[extensional_def]
  \\ simp[chu_morphism_map_component_equality]
  \\ simp[FUN_EQ_THM, PULL_FORALL]
  \\ simp[mor1_def, mor2_def, mk_chu_morphism_def]
  \\ simp[guest_def, restrict_def, PULL_EXISTS, POW_EQNS]
  \\ dsimp[]
  \\ qmatch_assum_rename_tac`z ⊆ _`
  \\ Cases_on`z = {}` \\ fs[]
  >- ( disj1_tac \\ rw[] \\ metis_tac[] )
  \\ `z = guests DIFF {x; y}`
  by (
    fs[SUBSET_DEF, GSYM MEMBER_NOT_EMPTY]
    \\ simp[EXTENSION]
    \\ gvs[guests_def]
    \\ metis_tac[])
  \\ disj2_tac
  \\ rw[] \\ rw[]
  \\ rw[EXTENSION]
  \\ metis_tac[]
QED

Theorem mor1_neq_mor2:
  mor1 x y ≠ mor2 x y
Proof
  rw[mor1_def, mor2_def, morphism_component_equality]
  \\ rw[chu_morphism_map_component_equality]
  \\ fs[mk_chu_morphism_def]
  \\ fs[restrict_def]
  \\ fs[FUN_EQ_THM]
  \\ dsimp[guest_def, POW_EQNS]
  \\ qexists_tac`encode_set ∅`
  \\ simp[]
  \\ simp[guests_def]
  \\ rw[]
QED

Theorem tensor_guests_iso:
  x ∈ guests ∧ y ∈ guests ∧ x ≠ y ⇒
  tensor (guest x) (guest y) ≅
    (swap (guest (CHOICE (guests DIFF {x;y})))) -: chu party_world
Proof
  rw[iso_objs_thm]
  \\ qmatch_goalsub_abbrev_tac`swap (guest z)`
  \\ qexists_tac`mk_chu_morphism (tensor (guest x) (guest y)) (swap (guest z))
       <| map_agent := λp. let (a,b) = decode_pair p in
            encode_set (decode_set a ∪ decode_set b);
          map_env := λe.
          encode_morphism
            ((if e = encode_set ∅ then mor1 else mor2) x y )|>`
  \\ `z ∈ guests ∧ z ≠ x ∧ z ≠ y`
  by (
    simp[Abbr`z`]
    \\ qmatch_goalsub_abbrev_tac`CHOICE s`
    \\ `CHOICE s ∈ s`
    by(
      irule CHOICE_DEF
      \\ simp[Abbr`s`, GSYM MEMBER_NOT_EMPTY]
      \\ gs[guests_def]
      \\ dsimp[])
    \\ fs[Abbr`s`])
  \\ `guests = {x;y;z}`
  by ( fs[guests_def] \\ gvs[]
       \\ rw[EXTENSION] \\ metis_tac[])
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ conj_asm1_tac
    >- (
      dsimp[tensor_def, hom_def] \\ rw[]
      \\ metis_tac[mor1_maps_to, mor2_maps_to] )
    \\ conj_asm1_tac
    >- (
      simp[tensor_def, PULL_EXISTS, EXISTS_PROD]
      \\ simp[guest_def, PULL_EXISTS]
      \\ dsimp[POW_EQNS]
      \\ qexists_tac`{x}∪{y}`
      \\ qexists_tac`{x}`
      \\ qexists_tac`{y}`
      \\ qexists_tac`{}` \\ simp[]
      \\ simp[IN_POW, SUBSET_DEF])
    \\ simp[tensor_eval]
    \\ simp[tensor_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[Ntimes guest_def 2, PULL_EXISTS]
    \\ rpt gen_tac
    \\ DEP_REWRITE_TAC[Q.GEN`w`decode_encode_chu_morphism]
    \\ conj_tac >- metis_tac[mor1_maps_to, mor2_maps_to]
    \\ simp[guest_eval]
    \\ simp[guest_def, PULL_EXISTS]
    \\ simp[DELETE_INSERT]
    \\ dsimp[POW_EQNS]
    \\ simp[mor1_def, mor2_def, mk_chu_morphism_def, restrict_def, guest_def]
    \\ dsimp[POW_EQNS]
    \\ rw[] \\ rw[] \\ gs[]
    \\ fs[EXTENSION] \\ metis_tac[] )
  \\ simp[chu_iso_bij]
  \\ fs[maps_to_in_chu]
  \\ fs[is_chu_morphism_def, mk_chu_morphism_def]
  \\ fs[restrict_def]
  \\ simp[BIJ_DEF, INJ_DEF, SURJ_DEF]
  \\ simp[tensor_def, PULL_EXISTS, EXISTS_PROD]
  \\ simp[Ntimes guest_def 9, hom_def, PULL_EXISTS]
  \\ qpat_assum`_ = guests`(SUBST1_TAC o SYM)
  \\ simp[DELETE_INSERT]
  \\ dsimp[POW_EQNS]
  \\ rpt disj1_tac
  \\ conj_tac >- (simp[EXTENSION] \\ metis_tac[])
  \\ conj_tac >- metis_tac[decode_encode_chu_morphism,
                           mor1_neq_mor2, mor1_maps_to, mor2_maps_to]
  \\ rpt strip_tac
  \\ drule_then (drule_then (drule_then
       (drule_then mp_tac o
        Q.GEN`m` o #1 o EQ_IMP_RULE o SPEC_ALL))) maps_to_swap_guest
  \\ dsimp[]
  \\ simp[guest_def, PULL_EXISTS]
  \\ dsimp[POW_EQNS]
QED

Theorem tensor_jack_kate:
  tensor jack kate ≅ swap luke -: chu party_world
Proof
  rw[jack_def, kate_def, luke_def]
  \\ `"L" = CHOICE (guests DIFF {"J";"K"})`
  by simp[guests_def]
  \\ pop_assum SUBST1_TAC
  \\ irule tensor_guests_iso
  \\ simp[guests_def]
QED

val _ = export_theory();
