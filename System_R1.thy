(*
   Authors: Asta Halkjær From, Agnes Moesgård Eschen & Jørgen Villadsen, DTU Compute
*)

theory System_R1 imports System_L1 begin

text \<open>System R from Alfred Whitehead, Bertrand Russell: Principia Mathematica
                                                        (Second Ed. 1925-1927)\<close>

text \<open>Derivations are taken from: On Axiom Systems of Propositional Calculi. V
                                  by Kiyoshi Iseki and Shotaro Tanaka (1965)\<close>

inductive R (\<open>\<RR>\<close>) where
  R_MP: \<open>\<RR> q\<close> if \<open>\<RR> p\<close> and \<open>\<RR> (p \<rightarrow> q)\<close> |
  R_1:  \<open>\<RR> (p \<rightarrow> (q \<rightarrow> p))\<close> |
  R_2:  \<open>\<RR> ((p \<rightarrow> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close> |
  R_3:  \<open>\<RR> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r)))\<close> |
  R_4:  \<open>\<RR> ((\<sim> (\<sim> p)) \<rightarrow> p)\<close> |
  R_5:  \<open>\<RR> ((p \<rightarrow> (\<sim> p)) \<rightarrow> (\<sim> p))\<close> |
  R_6:  \<open>\<RR> ((p \<rightarrow> (\<sim> q)) \<rightarrow> (q \<rightarrow> (\<sim> p)))\<close>

lemma R_7: \<open>\<RR> (q \<rightarrow> (p \<rightarrow> p))\<close>
  using R_1 R_3 R_MP by metis

lemma R_8: \<open>\<RR> (p \<rightarrow> p)\<close>
  using R_1 R_7 R_MP by metis

lemma R_9: \<open>\<RR> (p \<rightarrow> (\<sim> (\<sim> p)))\<close>
  using R_6 R_8 R_MP by metis

lemma R_10: \<open>\<RR> ((q \<rightarrow> r) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close>
  using R_2 R_3 R_MP by metis

lemma R_11: \<open>\<RR> ((q \<rightarrow> (\<sim> (\<sim> p))) \<rightarrow> (q \<rightarrow> p))\<close>
  using R_4 R_10 R_MP by metis

lemma R_12: \<open>\<RR> (((\<sim> p) \<rightarrow> (\<sim> q)) \<rightarrow> (q \<rightarrow> p))\<close>
  using R_2 R_6 R_11 R_MP by metis

lemma R_13: \<open>\<RR> ((\<sim> p) \<rightarrow> (p \<rightarrow> q))\<close>
  using R_1 R_2 R_12 R_MP by metis

lemma R_14: \<open>\<RR> (p \<rightarrow> ((\<sim> p) \<rightarrow> q))\<close>
  using R_3 R_13 R_MP by metis

lemma R_15: \<open>\<RR> ((p \<rightarrow> (\<sim> (\<sim> q))) \<rightarrow> (p \<rightarrow> q))\<close>
  using R_4 R_10 R_MP by metis (* under substitution this lemma is the same as R_11 *)

lemma R_16: \<open>\<RR> (((\<sim> p) \<rightarrow> q) \<rightarrow> ((\<sim> p) \<rightarrow> (\<sim> (\<sim> q))))\<close>
  using R_9 R_10 R_MP by metis

lemma R_17: \<open>\<RR> (((\<sim> p) \<rightarrow> q) \<rightarrow> ((\<sim> q) \<rightarrow> p))\<close>
  using R_2 R_12 R_16 R_MP by metis

lemma R_18: \<open>\<RR> ((p \<rightarrow> q) \<rightarrow> ((\<sim> (\<sim> p)) \<rightarrow> q))\<close>
  using R_2 R_4 R_MP by metis

lemma R_19: \<open>\<RR> ((((\<sim> (\<sim> p)) \<rightarrow> q) \<rightarrow> r) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> r))\<close>
  using R_2 R_18 R_MP by metis

lemma R_20: \<open>\<RR> ((((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)) \<rightarrow> s) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> s))\<close>
  using R_2 R_MP by metis

lemma R_21: \<open>\<RR> ((p \<rightarrow> q) \<rightarrow> (((p \<rightarrow> r) \<rightarrow> s) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> s)))\<close>
  using R_2 R_20 R_MP by metis

lemma R_22: \<open>\<RR> (((p \<rightarrow> r) \<rightarrow> s) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> s)))\<close>
  using R_3 R_21 R_MP by metis

lemma R_23: \<open>\<RR> ((((\<sim> q) \<rightarrow> (\<sim> p)) \<rightarrow> r) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> r))\<close>
  using R_17 R_19 R_22 R_MP by metis

lemma R_24: \<open>\<RR> (((\<sim> p) \<rightarrow> p) \<rightarrow> (\<sim> (\<sim> p)))\<close>
  using R_5 R_23 R_MP by metis

lemma R_25: \<open>\<RR> (((\<sim> p) \<rightarrow> p) \<rightarrow> p)\<close>
  using R_15 R_24 R_MP by metis

theorem R_iff_L1: \<open>\<RR> p \<longleftrightarrow> \<turnstile> p\<close>
proof
  have L1_R_1: \<open>\<turnstile> (p \<rightarrow> (q \<rightarrow> p))\<close> for p q
    using L1_completeness by simp
  have L1_R_2: \<open>\<turnstile> ((p \<rightarrow> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close> for p q r
    using L1_completeness by simp
  have L1_R_3: \<open>\<turnstile> ((p \<rightarrow> (q \<rightarrow> r)) \<rightarrow> (q \<rightarrow> (p \<rightarrow> r)))\<close> for p q r
    using L1_completeness by simp
  have L1_R_4: \<open>\<turnstile> ((\<sim> (\<sim> p)) \<rightarrow> p)\<close> for p
    using L1_completeness by simp
  have L1_R_5: \<open>\<turnstile> ((p \<rightarrow> (\<sim> p)) \<rightarrow> (\<sim> p))\<close> for p
    using L1_completeness by simp
  have L1_R_6: \<open>\<turnstile> ((p \<rightarrow> (\<sim> q)) \<rightarrow> (q \<rightarrow> (\<sim> p)))\<close> for p q
    using L1_completeness by simp
  show \<open>\<turnstile> p\<close> if \<open>\<RR> p\<close>
    using that by (induct) (metis MP, metis L1_R_1, metis L1_R_2, metis L1_R_3,
        metis L1_R_4, metis L1_R_5, metis L1_R_6)
  show \<open>\<RR> p\<close> if \<open>\<turnstile> p\<close>
    using that by (induct) (metis R_MP, metis R_2, metis R_25, metis R_14)
qed

theorem R_soundness: \<open>\<RR> p \<Longrightarrow> I \<Turnstile> p\<close>
  by (induct rule: R.induct) auto

theorem R_completeness: \<open>\<forall>I. (I \<Turnstile> p) \<Longrightarrow> \<RR> p\<close>
  using R_iff_L1 by (simp add: L1_completeness)

section \<open>Soundness and Completeness\<close>

theorem main: \<open>valid p = \<RR> p\<close>
  unfolding valid_def using R_soundness R_completeness by blast

lemmas R1 = R.intros main

end
