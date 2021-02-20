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

open HolKernel boolLib bossLib boolSimps Parse
  pairTheory pred_setTheory categoryTheory
  cf0Theory matrixTheory matrixLib cf1Theory cf2Theory cf4Theory

val _ = new_theory"ex4";

Definition prime_env_def:
  prime_env = {"P"; "N"}
End

Definition prime_agent_sensitive_def:
  prime_agent_sensitive = {"A"; "I"}
End

Definition prime_agent_coarse_def:
  prime_agent_coarse = prime_env ∪ prime_agent_sensitive
End

Theorem prime_agent_coarse_eq = CONV_RULE(RAND_CONV EVAL) prime_agent_coarse_def

Definition prime_agent_fine_def:
  prime_agent_fine = IMAGE (UNCURRY(++)) (prime_agent_coarse × {"H"; "C"}) DIFF {"AC"; "IC"}
End

Theorem prime_agent_fine_eq = CONV_RULE(RAND_CONV EVAL) prime_agent_fine_def

Definition prime_world_def:
  prime_world = IMAGE (λ(x,y,z). x ++ y++ z) (prime_env × prime_agent_sensitive × {"H"; "C"})
End

Theorem prime_world_eq = CONV_RULE(RAND_CONV EVAL) prime_world_def

Definition prime_cf_def:
  prime_cf = mk_cf <|
    world := prime_world;
    agent := prime_agent_fine;
    env := prime_env;
    eval := λa e. e ++ (if e = TAKE 1 a then "A" else
                        if TAKE 1 a ∈ {"P"; "N"} then "I"
                        else TAKE 1 a) ++ (DROP 1 a) |>
End

Theorem wf_prime_cf[simp]:
  wf prime_cf
Proof
  EVAL_TAC \\ rw[] \\ EVAL_TAC \\ pop_assum mp_tac \\ EVAL_TAC
QED

Definition prime_world_coarse_def:
  prime_world_coarse = IMAGE (TAKE 2) prime_world
End

Theorem prime_world_coarse_eq = CONV_RULE(RAND_CONV EVAL) prime_world_coarse_def

Theorem move_fn_prime_cf_matrix:
  cf_matrix (move_fn (TAKE 2) prime_world_coarse prime_cf) =
             (* N *) (* P *)
    (* AH *) [["NA"; "PA"];
    (* IH *)  ["NI"; "PI"];
    (* NC *)  ["NA"; "PI"];
    (* NH *)  ["NA"; "PI"];
    (* PC *)  ["NI"; "PA"];
    (* PH *)  ["NI"; "PA"]]
Proof
  simp[cf_matrix_def]
  \\ simp[EVAL``prime_cf.env``, EVAL``prime_cf.agent``]
  \\ qsort_set_to_list_tac
  \\ EVAL_TAC
QED

Theorem biextensional_collapse_move_fn_prime_cf_matrix:
  cf_matrix (biextensional_collapse (move_fn (TAKE 2) prime_world_coarse prime_cf)) =
            (* N *) (* P *)
    (* A *) [["NA"; "PA"];
    (* I *)  ["NI"; "PI"];
    (* N *)  ["NA"; "PI"];
    (* P *)  ["NI"; "PA"]]
Proof
  rw[biextensional_collapse_def]
  \\ simp[EVAL``prime_cf.env``, EVAL``prime_cf.agent``]
  \\ qmatch_goalsub_abbrev_tac`min_elt _ s`
  \\ `s = { "PH"; "PC"}`
  by (
    simp[Abbr`s`, SET_EQ_SUBSET, SUBSET_DEF] \\ rw[]
    \\ TRY(pop_assum mp_tac) \\ EVAL_TAC \\ srw_tac[DNF_ss][] )
  \\ `FINITE s ∧ s ≠ ∅` by simp[]
  \\ simp[rep_HD_QSORT_SET_TO_LIST]
  \\ rpt(pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac`min_elt _ s`
  \\ `s = { "PH"; "PC"}`
  by (
    simp[Abbr`s`, SET_EQ_SUBSET, SUBSET_DEF] \\ rw[]
    \\ TRY(pop_assum mp_tac) \\ EVAL_TAC \\ srw_tac[DNF_ss][] )
  \\ `FINITE s ∧ s ≠ ∅` by simp[]
  \\ simp[rep_HD_QSORT_SET_TO_LIST]
  \\ rpt(pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac`min_elt _ s`
  \\ `s = { "NH"; "NC"}`
  by (
    simp[Abbr`s`, SET_EQ_SUBSET, SUBSET_DEF] \\ rw[]
    \\ TRY(pop_assum mp_tac) \\ EVAL_TAC \\ srw_tac[DNF_ss][] )
  \\ `FINITE s ∧ s ≠ ∅` by simp[]
  \\ simp[rep_HD_QSORT_SET_TO_LIST]
  \\ rpt(pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac`min_elt _ s`
  \\ `s = { "NH"; "NC"}`
  by (
    simp[Abbr`s`, SET_EQ_SUBSET, SUBSET_DEF] \\ rw[]
    \\ TRY(pop_assum mp_tac) \\ EVAL_TAC \\ srw_tac[DNF_ss][] )
  \\ `FINITE s ∧ s ≠ ∅` by simp[]
  \\ simp[rep_HD_QSORT_SET_TO_LIST]
  \\ rpt(pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac`min_elt _ s`
  \\ `s = { "AH" }`
  by (
    simp[Abbr`s`, SET_EQ_SUBSET, SUBSET_DEF] \\ rw[]
    \\ TRY(pop_assum mp_tac) \\ EVAL_TAC \\ srw_tac[DNF_ss][] )
  \\ simp[]
  \\ rpt(pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac`min_elt _ s`
  \\ `s = { "IH" }`
  by (
    simp[Abbr`s`, SET_EQ_SUBSET, SUBSET_DEF] \\ rw[]
    \\ TRY(pop_assum mp_tac) \\ EVAL_TAC \\ srw_tac[DNF_ss][] )
  \\ simp[]
  \\ rpt(pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac`min_elt _ s`
  \\ `s = { "P" }`
  by (
    simp[Abbr`s`, SET_EQ_SUBSET, SUBSET_DEF] \\ rw[]
    \\ TRY(pop_assum mp_tac) \\ EVAL_TAC \\ srw_tac[DNF_ss][] )
  \\ simp[]
  \\ rpt(pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac`min_elt _ s`
  \\ `s = { "N" }`
  by (
    simp[Abbr`s`, SET_EQ_SUBSET, SUBSET_DEF] \\ rw[]
    \\ TRY(pop_assum mp_tac) \\ EVAL_TAC \\ srw_tac[DNF_ss][] )
  \\ simp[]
  \\ rpt(pop_assum kall_tac)
  \\ qsort_set_to_list_tac
  \\ CONV_TAC(PATH_CONV"lrrrrl"EVAL)
  \\ rw[cf_matrix_def]
  \\ qsort_set_to_list_tac
  \\ EVAL_TAC
QED

Theorem prime_cf_eval:
  prime_cf.eval a e =
  if a ∈ prime_cf.agent ∧ e ∈ prime_cf.env then
    e ++ (if e = TAKE 1 a then "A" else if TAKE 1 a ∈ {"P"; "N"} then "I"
          else TAKE 1 a) ++ DROP 1 a
  else ARB
Proof
  rw[prime_cf_def, mk_cf_def]
QED

Definition prime_outcomes_def:
  prime_outcomes w = { x | HD x = #"P" ∧ x ∈ w }
End

Theorem prime_obs_coarse:
  prime_outcomes prime_world_coarse ∈
  obs (move_fn (TAKE 2) prime_world_coarse prime_cf)
Proof
  rw[obs_def, prime_outcomes_def, Once prime_world_coarse_def]
  >- rw[prime_world_coarse_def, SUBSET_DEF]
  \\ rw[ifs_def, PULL_EXISTS]
  \\ qmatch_goalsub_abbrev_tac`c.eval`
  \\ qexists_tac`if HD a0 = #"P" ∨ HD a0 = #"A" then
                   if HD a1 = #"P" ∨ HD a1 = #"I" then
                     "PH" else "AH"
                 else
                   if HD a1 = #"P" ∨ HD a1 = #"I" then
                     "IH" else "NH"`
  \\ qmatch_goalsub_abbrev_tac`a ∈ _`
  \\ conj_asm1_tac
  >- rw[Abbr`a`, prime_cf_def, prime_agent_fine_eq]
  \\ simp[Abbr`c`, move_fn_def]
  \\ simp[prime_cf_eval]
  \\ pop_assum kall_tac
  \\ unabbrev_all_tac
  \\ gs[prime_cf_def]
  \\ rpt (pop_assum mp_tac)
  \\ simp[prime_env_def, prime_agent_fine_eq]
  \\ strip_tac \\ simp[] \\ strip_tac \\ simp[]
  \\ rpt strip_tac \\ simp[] \\ gvs[]
  \\ rpt(pop_assum mp_tac)
  \\ dsimp[prime_world_eq]
QED

Theorem prime_not_obs_fine:
  prime_outcomes prime_world ∉ obs prime_cf
Proof
  rw[obs_def, prime_outcomes_def]
  \\ CCONTR_TAC \\ fs[]
  \\ pop_assum mp_tac \\ simp[]
  \\ qexists_tac`"PC"`
  \\ qexists_tac`"NC"`
  \\ conj_tac >- rw[prime_cf_def, prime_agent_fine_eq]
  \\ rw[ifs_def]
  \\ CCONTR_TAC \\ fs[]
  \\ pop_assum mp_tac \\ simp[]
  \\ qexists_tac`if HD a = #"P" then "N" else "P"`
  \\ conj_asm1_tac >- rw[prime_cf_def, prime_env_def]
  \\ simp[prime_cf_eval]
  \\ qpat_x_assum`a ∈ _`mp_tac
  \\ simp[prime_cf_def, prime_agent_fine_eq]
  \\ strip_tac \\ simp[]
  \\ EVAL_TAC
QED

Theorem prime_cf_in_chu_objects[simp]:
  prime_cf ∈ chu_objects prime_world
Proof
  rw[prime_cf_def, in_chu_objects]
QED

Theorem prime_coarse_product:
  move_fn (TAKE 2) prime_world_coarse prime_cf ≃
  cfbot prime_world_coarse {x | HD x = #"P" ∧ x ∈ prime_world_coarse } &&
  cfbot prime_world_coarse {x | HD x = #"N" ∧ x ∈ prime_world_coarse }
  -: prime_world_coarse
Proof
  rw[homotopy_equiv_def]
  \\ qmatch_goalsub_abbrev_tac`_ :- pc → c1 && c2 -: _`
  \\ qexists_tac`mk_chu_morphism pc (c1 && c2)
       <| map_agent := λa. if HD a = #"A" then encode_pair ("PA", "NA")
                           else if HD a = #"I" then encode_pair ("PI", "NI")
                           else if HD a = #"P" then encode_pair ("PA", "NI")
                           else encode_pair ("PI", "NA");
          map_env := λe. sum_CASE (decode_sum e) (K"P") (K"N") |>`
  \\ qmatch_goalsub_abbrev_tac`_ o f -: _`
  \\ qexists_tac`mk_chu_morphism (c1 && c2) pc
       <| map_agent := λa.
            if a = encode_pair ("PA", "NA") then "AH"
            else if a = encode_pair ("PI", "NI") then "IH"
            else if a = encode_pair ("PA", "NI") then "PH"
            else "NH";
          map_env := λe.
            encode_sum (if e = "P" then (INL "") else (INR "")) |>`
  \\ qmatch_goalsub_abbrev_tac`g o f -: _`
  \\ `FINITE prime_world_coarse` by simp[prime_world_coarse_eq]
  \\ `pc ∈ chu_objects prime_world_coarse`
  by (
    simp[Abbr`pc`]
    \\ irule move_fn_in_chu_objects
    \\ simp[]
    \\ qexists_tac`prime_world`
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ rw[prime_world_eq, prime_world_coarse_eq] \\ rw[])
  \\ `c1 && c2 ∈ chu_objects prime_world_coarse`
  by (
    simp[Abbr`c1`, Abbr`c2`]
    \\ irule prod_in_chu_objects
    \\ simp[SUBSET_DEF] )
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu, GSYM CONJ_ASSOC, Abbr`f`]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ conj_asm1_tac
    >- (
      simp[prod_def, PULL_EXISTS]
      \\ simp[Abbr`c1`, Abbr`c2`, PULL_EXISTS, cfbot_def]
      \\ simp[Abbr`pc`, prime_cf_def, prime_env_def]
      \\ rw[] \\ rw[] )
    \\ conj_asm1_tac
    >- (
      simp[prod_def, EXISTS_PROD]
      \\ simp[Abbr`pc`, prime_cf_def, prime_agent_fine_eq]
      \\ simp[Abbr`c1`, Abbr`c2`, cfbot_def, prime_world_coarse_eq]
      \\ rw[] \\ rw[])
    \\ simp[prod_eval]
    \\ fs[Abbr`pc`]
    \\ simp[prime_cf_eval]
    \\ simp[prod_def, PULL_EXISTS]
    \\ dsimp[sum_eval_def]
    \\ simp[Abbr`c1`, Abbr`c2`, cfbot_def, cf1_def, mk_cf_def, prime_world_coarse_eq]
    \\ simp[prime_cf_def, prime_agent_fine_eq]
    \\ conj_tac \\ rpt strip_tac \\ simp[])
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu, Abbr`g`]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ conj_asm1_tac
    >- (
      simp[prod_def, EXISTS_PROD]
      \\ simp[Abbr`pc`, prime_cf_def, prime_agent_fine_eq]
      \\ simp[Abbr`c1`, Abbr`c2`, cfbot_def, prime_world_coarse_eq])
    \\ conj_asm1_tac
    >- (
      simp[prod_def, PULL_EXISTS, EXISTS_PROD]
      \\ simp[Abbr`c1`, Abbr`c2`, PULL_EXISTS, cfbot_def]
      \\ simp[Abbr`pc`, prime_cf_def, prime_env_def, prime_agent_fine_eq]
      \\ rw[] \\ rw[] )
    \\ simp[prod_eval]
    \\ simp[Abbr`pc`] \\ fs[]
    \\ simp[prime_cf_eval]
    \\ simp[prod_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[prime_cf_def, prime_env_def]
    \\ dsimp[sum_eval_def]
    \\ simp[Abbr`c1`, Abbr`c2`, cfbot_def, cf1_def, mk_cf_def, prime_world_coarse_eq]
    \\ conj_tac \\ rpt strip_tac \\ gs[])
  \\ qpat_assum`f :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`g :- _ → _ -: _`o mp_then Any strip_assume_tac)
  \\ qpat_assum`g :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`f :- _ → _ -: _`o mp_then Any strip_assume_tac)
  \\ simp[homotopic_id_map_env_id]
  \\ simp[restrict_def]
  \\ fs[Abbr`f`,Abbr`g`,mk_chu_morphism_def]
  \\ simp[restrict_def]
  \\ simp[Abbr`pc`]
  \\ simp[Once prime_cf_def]
  \\ dsimp[prime_env_def]
  \\ conj_tac
  >- ( simp[prod_def] \\ simp[Abbr`c1`, Abbr`c2`, cfbot_def] )
  \\ dsimp[Once prod_def, PULL_EXISTS]
  \\ simp[prime_cf_def, prime_env_def]
  \\ simp[Abbr`c1`, Abbr`c2`, cfbot_def]
QED

val _ = export_theory();
