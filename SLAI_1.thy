(*
  Authors: Asta Halkjær From, Agnes Moesgård Eschen & Jørgen Villadsen, DTU Compute
*)

theory SLAI_1 imports System_L1 begin

text \<open>Inspired by Larry Wos: Conquering the Meredith Single Axiom, J. Autom. Reas. 27:175–199 2001\<close>

inductive Single (\<open>\<tturnstile>\<close>) where
  MP: \<open>\<tturnstile> q\<close> if \<open>\<tturnstile> p\<close> and \<open>\<tturnstile> (p \<rightarrow> q)\<close> |
  AX: \<open>\<tturnstile> (((((p \<rightarrow> q) \<rightarrow> (\<sim> r \<rightarrow> \<sim> s)) \<rightarrow> r) \<rightarrow> t) \<rightarrow> ((t \<rightarrow> p) \<rightarrow> (s \<rightarrow> p)))\<close>

lemma L1_3: \<open>\<tturnstile> (p \<rightarrow> (\<sim> p \<rightarrow> q))\<close>
  using AX MP by metis

lemma 1: \<open>\<tturnstile> (((p \<rightarrow> q) \<rightarrow> r) \<rightarrow> (q \<rightarrow> r))\<close>
  using AX MP by metis

lemma 2: \<open>\<tturnstile> (p \<rightarrow> (((q \<rightarrow> p) \<rightarrow> r) \<rightarrow> (s \<rightarrow> r)))\<close>
  using 1 AX MP by metis

lemma 3: \<open>\<tturnstile> (p \<rightarrow> (((q \<rightarrow> r) \<rightarrow> s) \<rightarrow> (((r \<rightarrow> t) \<rightarrow> (\<sim> s \<rightarrow> \<sim> q)) \<rightarrow> s)))\<close>
  using 1 2 AX MP by meson

lemma 4: \<open>\<tturnstile> (((p \<rightarrow> q) \<rightarrow> (r \<rightarrow> (s \<rightarrow> (q \<rightarrow> t)))) \<rightarrow> (u \<rightarrow> (r \<rightarrow> (s \<rightarrow> (q \<rightarrow> t)))))\<close>
  using 2 3 AX MP by meson

lemma 5: \<open>\<tturnstile> (((p \<rightarrow> (\<sim> (\<sim> q) \<rightarrow> q)) \<rightarrow> r) \<rightarrow> r)\<close>
  using 1 4 AX MP by metis

lemma L1_2: \<open>\<tturnstile> ((\<sim> p \<rightarrow> p) \<rightarrow> p)\<close>
  using 1 4 5 AX MP by metis

lemma 6: \<open>\<tturnstile> (((p \<rightarrow> (q \<rightarrow> (\<sim> ((r \<rightarrow> (\<sim> (\<sim> s) \<rightarrow> s)) \<rightarrow> \<sim> q)))) \<rightarrow> t) \<rightarrow> t)\<close>
  using 4 5 AX MP by metis

lemma 7: \<open>\<tturnstile> (((((p \<rightarrow> (\<sim> (\<sim> q) \<rightarrow> q)) \<rightarrow> \<sim> (\<sim> r)) \<rightarrow> s) \<rightarrow> t) \<rightarrow> ((r \<rightarrow> s) \<rightarrow> t))\<close>
  using 6 AX MP by metis

lemma L1_1: \<open>\<tturnstile> ((p \<rightarrow> q) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> (p \<rightarrow> r)))\<close>
  using 7 AX MP by metis

theorem \<open>\<turnstile> p \<longleftrightarrow> \<tturnstile> p\<close>
proof
  show \<open>\<turnstile> p\<close> if \<open>\<tturnstile> p\<close>
    using that by induct (use System_L1.MP in fast, use L1_completeness in simp)
  show \<open>\<tturnstile> p\<close> if \<open>\<turnstile> p\<close>
    using that by induct (use MP in fast, rule L1_1, rule L1_2, rule L1_3)
qed

end
