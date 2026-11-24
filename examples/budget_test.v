(** Tests for step budgets: a fetch of a charged instruction consumes one
[step_credits 1]. *)
Require Import isla.aarch64.aarch64.

(** With one credit, the fetch goal that [li_wp_next_instr] produces for a
charged address is provable: the automation finds [instr_charged] and asks for
[step_credits 1]. *)
Lemma charged_fetch_one_credit `{!islaG Σ} `{!threadG} t :
  instr_charged 0x1000 t -∗
  step_credits 1 -∗
  (arch_pc_reg ↦ᵣ RVal_Bits (BV 64 0x1000) -∗ WPasm t) -∗
  arch_pc_reg ↦ᵣ RVal_Bits (BV 64 0x1000) -∗
  WPasm tnil.
Proof.
  iIntros "#Hi Hcredit Hwp HPC".
  iApply li_wp_next_instr. iExists _. iFrame "HPC".
  iExists 0x1000. iSplit; [done|].
  iExists (IKCharged t). rewrite /FindInstrKind /=. iFrame "Hi".
  iFrame "Hcredit".
  rewrite (_ : Z_to_bv 64 0x1000 = BV 64 0x1000); [|by apply bv_eq].
  iIntros "HPC". iApply ("Hwp" with "HPC").
Qed.

(** The same through [wp_next_instr_charged] directly. *)
Lemma charged_fetch_one_credit' `{!islaG Σ} `{!threadG} (PC : bv 64) t :
  instr_charged (bv_unsigned PC) t -∗
  step_credits 1 -∗
  ▷ (arch_pc_reg ↦ᵣ RVal_Bits PC -∗ WPasm t) -∗
  arch_pc_reg ↦ᵣ RVal_Bits PC -∗
  WPasm tnil.
Proof.
  iIntros "Hi Hcredit Hwp HPC".
  iApply (wp_next_instr_charged with "HPC Hi Hcredit Hwp").
Qed.

(** Without a credit, [wp_next_instr_charged] cannot be applied: its
premise [step_credits 1] is not available. *)
Goal ∀ `{!islaG Σ} `{!threadG} (PC : bv 64) t,
  instr_charged (bv_unsigned PC) t -∗
  ▷ (arch_pc_reg ↦ᵣ RVal_Bits PC -∗ WPasm t) -∗
  arch_pc_reg ↦ᵣ RVal_Bits PC -∗
  WPasm tnil.
Proof.
  iIntros (?????) "Hi Hwp HPC".
  Fail iApply (wp_next_instr_charged with "HPC Hi [] Hwp"); iAssumption.
Abort.

(** Semantic version: no proof of a program that fetches a charged
instruction can start from [step_credits 0]. If it could, adequacy would
bound the fetches of the one-step run below by 0, but that run performs one
charged fetch. *)
Lemma charged_fetch_needs_credit Σ `{!islaPreG Σ} (pc : bv 64) (t : isla_trace) :
  ¬ (∀ {HG : islaG Σ},
      ⊢ instr_table_raw {[pc := t]} -∗ charged_set {[pc]} -∗ step_credits 0 -∗
        backed_mem (dom (∅ : mem_map)) -∗ spec_trace (λ _, True%type) -∗
        ([∗ map] a↦b∈(∅ : mem_map), bv_unsigned a ↦ₘ b)
      ={⊤}=∗ [∗ list] rs ∈ [<[arch_pc_reg := RVal_Bits pc]> (∅ : reg_map)],
        ∀ (_ : threadG), ([∗ map] r↦v∈rs, r ↦ᵣ v) -∗ WPasm tnil).
Proof.
  move => Hwp.
  set regs := <[arch_pc_reg := RVal_Bits pc]> (∅ : reg_map).
  set σ0 := {| seq_instrs := {[pc := t]}; seq_mem := ∅; seq_charged := {[pc]}; seq_fetches := 0 |}.
  set θ1 := initial_local_state regs <| seq_trace := t |>.
  set σ1 := σ0 <| seq_fetches := 1%nat |>.
  have Hstep : nsteps 1 (initial_local_state <$> [regs], σ0) [] ([θ1], σ1).
  { apply (nsteps_l _ _ ([θ1], σ1) _ [] []); [|apply nsteps_refl].
    eapply step_atomic with (t1 := []) (t2 := []) (efs := []); [done|done|].
    apply (SeqStep _ _ (Some (LDone t)) t None); [done|constructor|].
    exists pc. split; [by rewrite /regs /= lookup_insert|].
    rewrite /σ0 /= lookup_insert. split_and!; [done..|].
    rewrite decide_True; [done|set_solver]. }
  have [_ [_ Hle]] := isla_budget_adequacy Σ {[pc := t]} ∅ [regs] (λ _, True) {[pc]} 0
    [θ1] σ1 [] 1 I Hwp Hstep.
  simpl in Hle. lia.
Qed.

Print Assumptions isla_budget_adequacy.
Print Assumptions charged_fetch_needs_credit.
Print Assumptions fetches_bound_steps.
