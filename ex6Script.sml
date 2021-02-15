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
  pairTheory pred_setTheory helperSetTheory rich_listTheory categoryTheory
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

Definition votes_world_def:
  votes_world = IMAGE encode_set (POW guests)
End

Theorem FINITE_votes_world[simp]:
  FINITE votes_world
Proof
  rw[votes_world_def]
QED

Definition guest_def:
  guest x = mk_cf <| world := votes_world;
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
  guest x ∈ chu_objects votes_world
Proof
  rw[guest_def, in_chu_objects, finite_cf_def]
  \\ rw[image_def, SUBSET_DEF]
  \\ DEP_REWRITE_TAC[decode_encode_set]
  \\ fs[IN_POW]
  \\ conj_tac >- metis_tac[SUBSET_FINITE, FINITE_DELETE, FINITE_SING, FINITE_guests]
  \\ simp[votes_world_def]
  \\ qmatch_goalsub_abbrev_tac`encode_set s`
  \\ qexists_tac`s` \\ simp[Abbr`s`, IN_POW]
  \\ fs[SUBSET_DEF]
QED

Theorem guest_world[simp]:
  (guest x).world = votes_world
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
  mor1 x y :- guest x → swap (guest y) -: chu votes_world
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
  mor2 x y :- guest x → swap (guest y) -: chu votes_world
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
  (m :- guest x → swap (guest y) -: chu votes_world ⇔
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
    (swap (guest (CHOICE (guests DIFF {x;y})))) -: chu votes_world
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
  tensor jack kate ≅ swap luke -: chu votes_world
Proof
  rw[jack_def, kate_def, luke_def]
  \\ `"L" = CHOICE (guests DIFF {"J";"K"})`
  by simp[guests_def]
  \\ pop_assum SUBST1_TAC
  \\ irule tensor_guests_iso
  \\ simp[guests_def]
QED

Definition majority_def:
  majority s = if CARD guests ≤ 2 * CARD (decode_set s) then "Y" else "N"
End

Definition party_world_def:
  party_world = {"Y";"N"}
End

Theorem FINITE_party_world[simp]:
  FINITE party_world
Proof
  rw[party_world_def]
QED

Theorem move_fn_majority_in_chu_objects[simp]:
  x ∈ guests ⇒
  move_fn majority party_world (guest x) ∈ chu_objects party_world
Proof
  strip_tac
  \\ irule move_fn_in_chu_objects
  \\ rw[]
  \\ qexists_tac`votes_world`
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ rw[majority_def]
  \\ rw[party_world_def]
QED

Definition guest_party_def:
  guest_party = mk_cf <| world := party_world;
    agent := {"";" "};
    env := {"";" ";"  "};
    eval := λa e. if (LENGTH a + LENGTH e < 2) then "N" else "Y" |>
End

Theorem guest_party_eval:
  guest_party.eval a e =
  if a ∈ guest_party.agent ∧ e ∈ guest_party.env then
    if (LENGTH a + LENGTH e < 2) then "N" else "Y"
  else ARB
Proof
  rw[guest_party_def, mk_cf_def]
QED

Theorem guest_party_world[simp]:
  guest_party.world = party_world
Proof
  rw[guest_party_def]
QED

Theorem guest_party_in_chu_objects[simp]:
  guest_party ∈ chu_objects party_world
Proof
  rw[in_chu_objects, guest_party_def, finite_cf_def]
  \\ rw[image_def, SUBSET_DEF]
  \\ rw[party_world_def]
QED

Theorem CARD_guests:
  CARD guests = 3
Proof
  rw[guests_def]
QED

Theorem move_fn_majority_guest_equiv_party:
  x ∈ guests ⇒
  move_fn majority party_world (guest x) ≃ guest_party -: party_world
Proof
  rw[homotopy_equiv_def]
  \\ qmatch_goalsub_abbrev_tac`_ :- px → gp -: _`
  \\ qexists_tac`mk_chu_morphism px gp
       <| map_agent := flip REPLICATE #" " o CARD o decode_set;
          map_env := λe.
            encode_set (@s. s ⊆ guests DELETE x ∧ CARD s = LENGTH e) |>`
  \\ qmatch_goalsub_abbrev_tac`_ o f -: _`
  \\ qexists_tac`mk_chu_morphism gp px
       <| map_agent := λa. encode_set (if a = "" then ∅ else {x});
          map_env := flip REPLICATE #" " o CARD o decode_set |>`
  \\ qmatch_goalsub_abbrev_tac`g o _ -: _`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu, Abbr`px`, Abbr`gp`]
    \\ simp[Abbr`f`, is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ conj_asm1_tac
    >- (
      simp[guest_def, IN_POW]
      \\ rpt strip_tac
      \\ SELECT_ELIM_TAC
      \\ reverse conj_tac >- metis_tac[]
      \\ qpat_x_assum`x ∈ _`mp_tac
      \\ simp [GSYM IN_POW]
      \\ simp[guests_def, DELETE_INSERT]
      \\ fs[guest_party_def]
      \\ strip_tac \\ simp[POW_EQNS]
      \\ dsimp[])
    \\ conj_asm1_tac
    >- (
      dsimp[guest_def, PULL_EXISTS, POW_EQNS, REPLICATE_compute]
      \\ simp[guest_party_def])
    \\ simp[move_fn_def]
    \\ simp[guest_eval, guest_party_eval]
    \\ rpt gen_tac
    \\ strip_tac
    \\ SELECT_ELIM_TAC
    \\ conj_tac
    >- (
      qpat_x_assum`x ∈ _`mp_tac
      \\ simp [GSYM IN_POW]
      \\ simp[guests_def, DELETE_INSERT]
      \\ fs[guest_party_def]
      \\ strip_tac \\ dsimp[POW_EQNS])
    \\ rpt strip_tac
    \\ simp[majority_def]
    \\ DEP_REWRITE_TAC[decode_encode_set]
    \\ conj_asm1_tac >- metis_tac[FINITE_guests, FINITE_DELETE, SUBSET_FINITE]
    \\ simp[]
    \\ conj_asm1_tac >- fs[guest_def, POW_EQNS]
    \\ DEP_REWRITE_TAC[CARD_UNION_DISJOINT]
    \\ simp[CARD_guests]
    \\ conj_tac >- (fs[guest_def, POW_EQNS, SUBSET_DEF] \\ metis_tac[])
    \\ rw[])
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu, Abbr`px`, Abbr`gp`]
    \\ simp[Abbr`g`, is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ conj_asm1_tac
    >- (
      qpat_x_assum`x ∈ _`mp_tac
      \\ simp [guest_def, GSYM IN_POW, PULL_EXISTS]
      \\ simp[guests_def, DELETE_INSERT]
      \\ rw[POW_EQNS] \\ rw[REPLICATE_compute, guest_party_def])
    \\ conj_asm1_tac
    >- rw[guest_def, POW_EQNS]
    \\ simp[move_fn_def]
    \\ simp[guest_party_eval]
    \\ simp[guest_eval]
    \\ simp[majority_def, CARD_guests]
    \\ rpt gen_tac \\ strip_tac
    \\ DEP_REWRITE_TAC[decode_encode_set]
    \\ DEP_REWRITE_TAC[CARD_UNION_DISJOINT]
    \\ conj_asm1_tac >- (
      fs[guest_def]
      \\ fs[IN_POW]
      \\ DEP_REWRITE_TAC[decode_encode_set]
      \\ conj_asm1_tac
      >- metis_tac[decode_encode_set, FINITE_DELETE,
                   FINITE_guests, SUBSET_FINITE]
      \\ rw[]
      \\ gs[SUBSET_DEF]
      \\ metis_tac[])
    \\ fs[]
    \\ Cases_on`a = ""` \\ rw[]
    \\ gs[guest_party_def])
  \\ qpat_assum`f :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`g :- _ → _ -: _` o mp_then Any strip_assume_tac)
  \\ qpat_assum`g :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`f :- _ → _ -: _` o mp_then Any strip_assume_tac)
  \\ simp[homotopic_id_map_agent_id, Abbr`px`, Abbr`gp`]
  \\ simp[restrict_def]
  \\ simp[Abbr`g`, Abbr`f`, mk_chu_morphism_def]
  \\ simp[restrict_def]
  \\ conj_tac
  >- (
    simp[Once guest_def, PULL_EXISTS]
    \\ dsimp[POW_EQNS]
    \\ rw[guest_party_def, REPLICATE_compute] )
  \\ simp[Once guest_party_def]
  \\ simp[Once guest_def, POW_EQNS]
  \\ dsimp[REPLICATE_compute]
QED

Theorem move_fn_majority_tensor_guests_equiv_swap_party:
  x ∈ guests ∧ y ∈ guests ∧ x ≠ y ⇒
  move_fn majority party_world (tensor (guest x) (guest y)) ≃ swap guest_party
  -: party_world
Proof
  strip_tac
  \\ qmatch_goalsub_abbrev_tac`p (tensor _ _)`
  \\ irule homotopy_equiv_trans
  \\ qabbrev_tac`z = CHOICE (guests DIFF {x; y})`
  \\ qexists_tac`p (swap (guest z))`
  \\ conj_tac
  >- (
    qunabbrev_tac`p`
    \\ irule homotopy_equiv_move_fn
    \\ simp[]
    \\ qexists_tac`votes_world`
    \\ simp[SUBSET_DEF, PULL_EXISTS, majority_def]
    \\ rw[party_world_def]
    \\ irule iso_homotopy_equiv
    \\ qunabbrev_tac`z`
    \\ irule tensor_guests_iso
    \\ simp[] )
  \\ simp[Abbr`p`, move_fn_swap]
  \\ DEP_REWRITE_TAC[homotopy_equiv_swap]
  \\ `z ∈ guests`
  by ( simp[Abbr`z`] \\ gs[guests_def] )
  \\ simp[move_fn_majority_guest_equiv_party]
QED

Theorem move_fn_majority_tensor_not_preserved:
  x ∈ guests ∧ y ∈ guests ∧ x ≠ y ⇒
  let p = move_fn majority party_world in
  ¬ (p (tensor (guest x) (guest y)) ≃ tensor (p (guest x)) (p (guest y))
     -: party_world)
Proof
  strip_tac
  \\ BasicProvers.LET_ELIM_TAC
  \\ strip_tac
  \\ `swap guest_party ≃ tensor guest_party guest_party -: party_world`
  by (
    metis_tac[move_fn_majority_tensor_guests_equiv_swap_party,
              move_fn_majority_guest_equiv_party,
              homotopy_equiv_trans, homotopy_equiv_sym,
              homotopy_equiv_tensor])
  \\ pop_assum mp_tac
  \\ simp[homotopy_equiv_def]
  \\ CCONTR_TAC \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`f :- swap gp → tgp -: _`
  \\ `∃e. e ∈ tgp.env ∧
          ∀a. a ∈ tgp.agent ⇒ tgp.eval a e = "N"`
  by(
    simp[Abbr`tgp`, tensor_eval]
    \\ simp[Once tensor_def, PULL_EXISTS, hom_def]
    \\ qexists_tac`mk_chu_morphism gp (swap gp) <|
         map_agent := K""; map_env := K"" |>`
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu, Abbr`gp`]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[guest_party_eval]
      \\ simp[guest_party_def]
      \\ rpt gen_tac \\ strip_tac \\ simp[])
    \\ DEP_REWRITE_TAC[Q.GEN`w`decode_encode_chu_morphism]
    \\ conj_tac >- metis_tac[]
    \\ simp[tensor_def, PULL_EXISTS, EXISTS_PROD, hom_def]
    \\ simp[mk_chu_morphism_def, restrict_def]
    \\ simp[Abbr`gp`, guest_party_eval]
    \\ simp[guest_party_def]
    \\ rpt gen_tac \\ strip_tac \\ simp[])
  \\ `∀a. a ∈ gp.env ⇒ (swap gp).eval a (f.map.map_env e) = "N"`
  by metis_tac[swap_components, maps_to_in_chu, is_chu_morphism_def]
  \\ `f.map.map_env e ∈ gp.agent`
  by metis_tac[swap_components, maps_to_in_chu, is_chu_morphism_def]
  \\ pop_assum mp_tac
  \\ first_x_assum(qspec_then`"  "`mp_tac)
  \\ simp[Abbr`gp`, guest_party_def, mk_cf_def, PULL_EXISTS]
  \\ IF_CASES_TAC \\ fs[]
QED

(* TODO comparison to example with coins and dictators voting rule *)

val _ = export_theory();
