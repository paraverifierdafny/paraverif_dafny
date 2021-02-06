(*  Title:      HOL/Auth/n_mutualExSimp_lemma_on_inv__4.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_mutualExSimp Protocol Case Study*} 

theory n_mutualExSimp_lemma_on_inv__4 imports n_mutualExSimp_base
begin
section{*All lemmas on causal relation between inv__4 and some rule r*}
lemma n_CritVsinv__4:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_Crit  i)" and
a2: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__4  p__Inv4)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_Crit  i" apply fastforce done
from a2 obtain p__Inv4 where a2:"p__Inv4\<le>N\<and>f=inv__4  p__Inv4" apply fastforce done
have "(i=p__Inv4)\<or>(i~=p__Inv4)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv4)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv4)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_ExitVsinv__4:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_Exit  i)" and
a2: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__4  p__Inv4)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_Exit  i" apply fastforce done
from a2 obtain p__Inv4 where a2:"p__Inv4\<le>N\<and>f=inv__4  p__Inv4" apply fastforce done
have "(i=p__Inv4)\<or>(i~=p__Inv4)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv4)"
  have "?P3 s"
  apply (cut_tac a1 a2 b1, simp, rule_tac x="(neg (andForm (eqn (IVar (Para (Ident ''n'') p__Inv4)) (Const C)) (eqn (IVar (Ident ''x'')) (Const true))))" in exI, auto) done
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv4)"
  have "?P2 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_IdleVsinv__4:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_Idle  i)" and
a2: "(\<exists> p__Inv4. p__Inv4\<le>N\<and>f=inv__4  p__Inv4)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_Idle  i" apply fastforce done
from a2 obtain p__Inv4 where a2:"p__Inv4\<le>N\<and>f=inv__4  p__Inv4" apply fastforce done
have "(i=p__Inv4)\<or>(i~=p__Inv4)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv4)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv4)"
  have "?P3 s"
  apply (cut_tac a1 a2 b1, simp, rule_tac x="(neg (andForm (eqn (IVar (Para (Ident ''n'') p__Inv4)) (Const E)) (eqn (IVar (Para (Ident ''n'') i)) (Const E))))" in exI, auto) done
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed
end
