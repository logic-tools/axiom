(*
   Authors: Asta Halkjær From, Agnes Moesgård Eschen & Jørgen Villadsen, DTU Compute
*)

theory System_S2 imports System_S0 begin

text \<open>System S2 from Boleslaw Sobocinski: Note on a Problem of Paul Barnays (1955) \<close>

text \<open>Derivations are taken from the above paper\<close>

inductive S2 (\<open>\<SS>\<^sub>2\<close>) where
  S2_MP: \<open>\<SS>\<^sub>2 q\<close> if \<open>\<SS>\<^sub>2 p\<close> and \<open>\<SS>\<^sub>2 (p \<rightarrow> q)\<close> |
  S2_1:  \<open>\<SS>\<^sub>2 (p \<rightarrow> (q \<rightarrow> (r \<rightarrow> p)))\<close> |
  S2_2:  \<open>\<SS>\<^sub>2 ((p \<rightarrow> q) \<rightarrow> ((\<sim> q) \<rightarrow> (p \<rightarrow> r)))\<close> |
  S2_3:  \<open>\<SS>\<^sub>2 (((\<sim> p) \<rightarrow> q) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> q))\<close>

lemma S2_4: \<open>\<SS>\<^sub>2 ((\<sim> (q \<rightarrow> (r \<rightarrow> p))) \<rightarrow> (p \<rightarrow> s))\<close>
  using S2_1 S2_2 S2_MP by metis

lemma S2_5: \<open>\<SS>\<^sub>2 (p \<rightarrow> (q \<rightarrow> (r \<rightarrow> (s \<rightarrow> p))))\<close>
  using S2_1 S2_3 S2_4 S2_MP by metis

lemma S2_6: \<open>\<SS>\<^sub>2 (p \<rightarrow> (q \<rightarrow> (r \<rightarrow> (s \<rightarrow> (t \<rightarrow> p)))))\<close>
  using S2_3 S2_4 S2_MP by metis

lemma S2_7: \<open>\<SS>\<^sub>2 ((\<sim> ((\<sim> q) \<rightarrow> (p \<rightarrow> r)) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> s)))\<close>
  using S2_2 S2_MP by metis

lemma S2_8: \<open>\<SS>\<^sub>2 ((p \<rightarrow> q) \<rightarrow> (s \<rightarrow> (t \<rightarrow> (v \<rightarrow> ((\<sim> q) \<rightarrow> (p \<rightarrow> r))))))\<close>
  using S2_3 S2_6 S2_7 S2_MP by metis

lemma S2_9: \<open>\<SS>\<^sub>2 ((\<sim> ((p \<rightarrow> q) \<rightarrow> q)) \<rightarrow> (((\<sim> p) \<rightarrow> q) \<rightarrow> r))\<close>
  using S2_2 S2_3 S2_MP by metis

lemma S2_10: \<open>\<SS>\<^sub>2 (((\<sim> p) \<rightarrow> q) \<rightarrow> (s \<rightarrow> (t \<rightarrow> ((\<sim> q) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> r)))))\<close>
  using S2_3 S2_8 S2_9 S2_MP by metis

lemma S2_11: \<open>\<SS>\<^sub>2 (((\<sim> p) \<rightarrow> q) \<rightarrow> (r \<rightarrow> (s \<rightarrow> ((p \<rightarrow> q) \<rightarrow> q))))\<close>
  using S2_3 S2_5 S2_9 S2_MP by metis

lemma S2_12: \<open>\<SS>\<^sub>2 ((p \<rightarrow> q) \<rightarrow> (s \<rightarrow> ((q \<rightarrow> (p \<rightarrow> r)) \<rightarrow> (p \<rightarrow> r))))\<close>
  using S2_3 S2_7 S2_11 S2_MP by metis

lemma S2_13: \<open>\<SS>\<^sub>2 ((\<sim> q) \<rightarrow> (p \<rightarrow> (\<sim> (p \<rightarrow> q))))\<close>
  using S2_1 S2_2 S2_3 S2_MP by metis

lemma S2_14: \<open>\<SS>\<^sub>2 ((\<sim> (p \<rightarrow> (\<sim> (p \<rightarrow> q)))) \<rightarrow> ((\<sim> q) \<rightarrow> r))\<close>
  using S2_2 S2_13 S2_MP by metis

lemma S2_15: \<open>\<SS>\<^sub>2 ((\<sim> q) \<rightarrow> (((\<sim> (p \<rightarrow> q)) \<rightarrow> (p \<rightarrow> r)) \<rightarrow> (p \<rightarrow> r)))\<close>
  using S2_3 S2_12 S2_14 S2_MP by metis

lemma S2_16: \<open>\<SS>\<^sub>2 (((\<sim> (p \<rightarrow> q)) \<rightarrow> (p \<rightarrow> q)) \<rightarrow> (p \<rightarrow> q))\<close>
  using S2_1 S2_3 S2_15 S2_MP by metis

lemma S2_17: \<open>\<SS>\<^sub>2 (p \<rightarrow> p)\<close>
  using S2_1 S2_12 S2_16 S2_MP by metis

lemma S2_18: \<open>\<SS>\<^sub>2 ((\<sim> p) \<rightarrow> (p \<rightarrow> q))\<close>
  using S2_2 S2_17 S2_MP by metis

lemma S2_19: \<open>\<SS>\<^sub>2 ((\<sim> (p \<rightarrow> q)) \<rightarrow> ((\<sim> p) \<rightarrow> r))\<close>
  using S2_2 S2_18 S2_MP by metis

lemma S2_20: \<open>\<SS>\<^sub>2 ((\<sim> p) \<rightarrow> (r \<rightarrow> (s \<rightarrow> (p \<rightarrow> q))))\<close>
  using S2_3 S2_5 S2_19 S2_MP by metis

lemma S2_21: \<open>\<SS>\<^sub>2 (p \<rightarrow> (q \<rightarrow> (\<sim> (\<sim> p))))\<close>
  using S2_1 S2_3 S2_19 S2_MP by metis

lemma S2_22: \<open>\<SS>\<^sub>2 (p \<rightarrow> (\<sim> (\<sim> p)))\<close>
  using S2_3 S2_18 S2_21 S2_MP by metis

lemma S2_23: \<open>\<SS>\<^sub>2 ((\<sim> (\<sim> p)) \<rightarrow> (t \<rightarrow> ((\<sim> q) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> r))))\<close>
  using S2_10 S2_12 S2_17 S2_18 S2_MP by metis

lemma S2_24: \<open>\<SS>\<^sub>2 (p \<rightarrow> ((\<sim> q) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> r)))\<close>
  using S2_12 S2_17 S2_22 S2_23 S2_MP by metis

lemma S2_25: \<open>\<SS>\<^sub>2 ((\<sim> q ) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> (p \<rightarrow> r)))\<close>
  using S2_3 S2_20 S2_24 S2_MP by metis

theorem S2_if_S0: \<open>\<SS>\<^sub>2 p\<close> if \<open>\<SS>\<^sub>0 p\<close> using that
  by (induct) (metis S2.intros(1), metis S2_5, metis S2_25, metis S2_3)

theorem S2_iff_L1: \<open>\<SS>\<^sub>2 p \<longleftrightarrow> \<turnstile> p\<close>
proof
  have S2_1: \<open>\<turnstile> (p \<rightarrow> (q \<rightarrow> (r \<rightarrow> p)))\<close> for p q r
    using L1_completeness by simp
  have S2_2: \<open>\<turnstile> ((p \<rightarrow> q) \<rightarrow> ((\<sim> q) \<rightarrow> (p \<rightarrow> r)))\<close> for p q r
    using L1_completeness by simp
  have S2_3: \<open>\<turnstile> (((\<sim> p) \<rightarrow> q) \<rightarrow> ((p \<rightarrow> q) \<rightarrow> q))\<close> for p q
    using L1_completeness by simp
  show \<open>\<turnstile> p\<close> if \<open>\<SS>\<^sub>2 p\<close>
    using that by (induct) (metis MP, metis S2_1, metis S2_2, metis S2_3)
  show \<open>\<SS>\<^sub>2 p\<close> if \<open>\<turnstile> p\<close>
    using that S0_if_L1 S2_if_S0 by simp
qed

theorem S2_soundness: \<open>\<SS>\<^sub>2 p \<Longrightarrow> I \<Turnstile> p\<close>
  by (induct rule: S2.induct) auto

theorem S2_completeness: \<open>\<forall>I. (I \<Turnstile> p) \<Longrightarrow> \<SS>\<^sub>2 p\<close>
  using S2_iff_L1 by (simp add: L1_completeness)

section \<open>Soundness and Completeness\<close>

theorem main: \<open>valid p = \<SS>\<^sub>2 p\<close>
  unfolding valid_def using S2_soundness S2_completeness by blast

lemmas S2 = S2.intros main

end
