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
  pred_setTheory
  cf0Theory matrixTheory matrixLib cf2Theory cf4Theory

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

Theorem prime_obs_coarse:
  { x | HD x = #"P" ∧ x ∈ IMAGE (TAKE 2) prime_world } ∈
  obs (move_fn (TAKE 2) prime_world_coarse prime_cf)
Proof
  rw[obs_def]
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
  { x | HD x = #"P" ∧ x ∈ prime_world } ∉ obs prime_cf
Proof
  rw[obs_def]
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

(* TODO: move_fn as a product *)

val _ = export_theory();
