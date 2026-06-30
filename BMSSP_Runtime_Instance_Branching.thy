theory BMSSP_Runtime_Instance_Branching
  imports BMSSP_Verified_Runtime BMSSP_Executable_Base_Case
begin

section \<open>A Second, Structurally Different Non-Vacuous Instance\<close>

text \<open>
  The path instance in \<open>BMSSP_Runtime_Instance\<close> certifies the runtime locale on
  a single chain.  To show that inhabitation does not rely on the degenerate
  linear shape, this theory discharges the same locale on a structurally
  different graph: the out-star \<open>1 \<leftarrow> 0 \<rightarrow> 2\<close> with two leaves, in which the
  source has outdegree two and there are two incomparable shortest paths.  The
  proof structure mirrors the path instance: the verified simple-walk
  enumerator pins down the unique shortest walk to each vertex.
\<close>

definition star_vs :: "nat list" where
  "star_vs = [0, 1, 2]"

definition star_es :: "(nat \<times> nat) list" where
  "star_es = [(0, 1), (0, 2)]"

definition star_V :: "nat set" where
  "star_V = set star_vs"

definition star_E :: "(nat \<times> nat) set" where
  "star_E = set star_es"

definition star_weight :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "star_weight u v = (if (u, v) \<in> star_E then 1 else 0)"

lemma star_vs_V: "set star_vs = star_V"
  unfolding star_V_def by (rule refl)

lemma star_es_E: "set star_es = star_E"
  unfolding star_E_def by (rule refl)

lemma star_positive_weight: "(u, v) \<in> star_E \<Longrightarrow> 0 < star_weight u v"
  unfolding star_weight_def by simp

lemma star_finite_weighted_digraph:
  "finite_weighted_digraph star_V star_E star_weight 0"
  unfolding finite_weighted_digraph_def
    star_V_def star_vs_def star_E_def star_es_def star_weight_def
  by auto

interpretation sfw: finite_weighted_digraph star_V star_E star_weight 0
  by (rule star_finite_weighted_digraph)

lemma star_walk_lists:
  "exec_simple_walks_betw star_vs star_es 0 0 = [[0]]"
  "exec_simple_walks_betw star_vs star_es 0 (Suc 0) = [[0, 1]]"
  "exec_simple_walks_betw star_vs star_es 0 2 = [[0, 2]]"
  by eval+

lemma star_simple_walk_sets:
  "{p. sfw.simple_walk_betw 0 p 0} = {[0]}"
  "{p. sfw.simple_walk_betw 0 p (Suc 0)} = {[0, 1]}"
  "{p. sfw.simple_walk_betw 0 p 2} = {[0, 2]}"
  using sfw.set_exec_simple_walks_betw[OF star_vs_V star_es_E, symmetric]
  by (simp_all add: star_walk_lists)

lemma star_walk_vertex:
  assumes "sfw.simple_walk_betw 0 p v"
  shows "v \<in> star_V"
proof -
  have walk_p: "sfw.walk p" and p_ne: "p \<noteq> []" and last_p: "last p = v"
    using assms unfolding sfw.simple_walk_betw_def sfw.walk_betw_def by auto
  have "v \<in> set p"
    using p_ne last_p by (metis last_in_set)
  moreover have "set p \<subseteq> star_V"
    using walk_p by (rule sfw.walk_set_subset)
  ultimately show ?thesis by blast
qed

lemma star_unique_shortest_walk:
  assumes "sfw.shortest_walk 0 p v" and "sfw.shortest_walk 0 q v"
  shows "p = q"
proof -
  have p: "sfw.simple_walk_betw 0 p v" and q: "sfw.simple_walk_betw 0 q v"
    using assms unfolding sfw.shortest_walk_def by blast+
  have vV: "v \<in> star_V"
    using p by (rule star_walk_vertex)
  have pm: "p \<in> {r. sfw.simple_walk_betw 0 r v}"
    using p by simp
  have qm: "q \<in> {r. sfw.simple_walk_betw 0 r v}"
    using q by simp
  from vV consider "v = 0" | "v = Suc 0" | "v = 2"
    unfolding star_V_def star_vs_def by auto
  then show "p = q"
  proof cases
    case 1 with pm qm show ?thesis by (simp add: star_simple_walk_sets)
  next
    case 2 with pm qm show ?thesis by (simp add: star_simple_walk_sets)
  next
    case 3 with pm qm show ?thesis by (simp add: star_simple_walk_sets)
  qed
qed

lemma star_all_reachable:
  assumes "v \<in> star_V"
  shows "sfw.reachable 0 v"
proof -
  from assms consider "v = 0" | "v = Suc 0" | "v = 2"
    unfolding star_V_def star_vs_def by auto
  then show ?thesis
  proof cases
    case 1
    have "[0] \<in> {r. sfw.simple_walk_betw 0 r 0}"
      by (simp add: star_simple_walk_sets)
    with 1 show ?thesis unfolding sfw.reachable_def by auto
  next
    case 2
    have "[0, 1] \<in> {r. sfw.simple_walk_betw 0 r (Suc 0)}"
      by (simp add: star_simple_walk_sets)
    with 2 show ?thesis unfolding sfw.reachable_def by auto
  next
    case 3
    have "[0, 2] \<in> {r. sfw.simple_walk_betw 0 r 2}"
      by (simp add: star_simple_walk_sets)
    with 3 show ?thesis unfolding sfw.reachable_def by auto
  qed
qed

interpretation susd: unique_shortest_digraph star_V star_E star_weight 0
  by unfold_locales (rule star_unique_shortest_walk)

lemma star_edge_outdegree: "susd.edge_outdegree_le 2"
  unfolding susd.edge_outdegree_le_def
proof
  fix u :: nat
  assume "u \<in> star_V"
  then consider "u = 0" | "u = Suc 0" | "u = 2"
    unfolding star_V_def star_vs_def by auto
  then show "card (susd.outgoing_edges {u}) \<le> 2"
  proof cases
    case 1
    then have "susd.outgoing_edges {u} = {(0, 1), (0, 2)}"
      unfolding susd.outgoing_edges_def by (auto simp: star_E_def star_es_def)
    then show ?thesis by (simp add: card_insert_if)
  next
    case 2
    then have "susd.outgoing_edges {u} = {}"
      unfolding susd.outgoing_edges_def by (auto simp: star_E_def star_es_def)
    then show ?thesis by simp
  next
    case 3
    then have "susd.outgoing_edges {u} = {}"
      unfolding susd.outgoing_edges_def by (auto simp: star_E_def star_es_def)
    then show ?thesis by simp
  qed
qed

interpretation sbr: bounded_reduced_positive_instance star_V star_E star_weight 0 2
  by unfold_locales
     (use star_positive_weight star_all_reachable star_edge_outdegree in auto)

text \<open>
  As with the path, the out-star yields the closed, assumption-free
  running-time bound and its verified-correct strengthening.  The two instances
  share no structural feature beyond the locale assumptions, so together they
  witness that the BMSSP runtime headline holds across genuinely different
  graph shapes.
\<close>

lemmas star_runtime_bigo_target =
  sbr.runtime_headline.bmssp_runtime_bigo_target

lemmas star_verified_runtime_bigo_target =
  sbr.runtime_headline.verified_bmssp_runtime_bigo_target

end
