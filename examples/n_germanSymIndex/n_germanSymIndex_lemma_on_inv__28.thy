(*  Title:      HOL/Auth/n_germanSymIndex_lemma_on_inv__28.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_germanSymIndex Protocol Case Study*} 

theory n_germanSymIndex_lemma_on_inv__28 imports n_germanSymIndex_base
begin
section{*All lemmas on causal relation between inv__28 and some rule r*}
lemma n_RecvReqSVsinv__28:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_RecvReqS N i)" and
a2: "(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__28  p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_RecvReqS N i" apply fastforce done
from a2 obtain p__Inv2 where a2:"p__Inv2\<le>N\<and>f=inv__28  p__Inv2" apply fastforce done
have "(i=p__Inv2)\<or>(i~=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv2)"
  have "?P3 s"
  apply (cut_tac a1 a2 b1, simp, rule_tac x="(neg (andForm (andForm (andForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E)))) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const Empty))) (eqn (IVar (Para (Ident ''ShrSet'') p__Inv2)) (Const true))) (eqn (IVar (Ident ''CurCmd'')) (Const Empty))))" in exI, auto) done
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv2)"
  have "?P3 s"
  apply (cut_tac a1 a2 b1, simp, rule_tac x="(neg (andForm (andForm (andForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E)))) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const Empty))) (eqn (IVar (Para (Ident ''ShrSet'') p__Inv2)) (Const true))) (eqn (IVar (Ident ''CurCmd'')) (Const Empty))))" in exI, auto) done
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_RecvReqEVsinv__28:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_RecvReqE N i)" and
a2: "(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__28  p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_RecvReqE N i" apply fastforce done
from a2 obtain p__Inv2 where a2:"p__Inv2\<le>N\<and>f=inv__28  p__Inv2" apply fastforce done
have "(i=p__Inv2)\<or>(i~=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv2)"
  have "?P3 s"
  apply (cut_tac a1 a2 b1, simp, rule_tac x="(neg (andForm (andForm (andForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E)))) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const Empty))) (eqn (IVar (Para (Ident ''ShrSet'') p__Inv2)) (Const true))) (eqn (IVar (Ident ''CurCmd'')) (Const Empty))))" in exI, auto) done
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv2)"
  have "?P3 s"
  apply (cut_tac a1 a2 b1, simp, rule_tac x="(neg (andForm (andForm (andForm (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (neg (eqn (IVar (Field (Para (Ident ''Cache'') p__Inv2) ''State'')) (Const E)))) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const Empty))) (eqn (IVar (Para (Ident ''ShrSet'') p__Inv2)) (Const true))) (eqn (IVar (Ident ''CurCmd'')) (Const Empty))))" in exI, auto) done
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_SendInv__part__0Vsinv__28:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_SendInv__part__0  i)" and
a2: "(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__28  p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_SendInv__part__0  i" apply fastforce done
from a2 obtain p__Inv2 where a2:"p__Inv2\<le>N\<and>f=inv__28  p__Inv2" apply fastforce done
have "(i=p__Inv2)\<or>(i~=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv2)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv2)"
  have "?P2 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_SendInv__part__1Vsinv__28:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_SendInv__part__1  i)" and
a2: "(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__28  p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_SendInv__part__1  i" apply fastforce done
from a2 obtain p__Inv2 where a2:"p__Inv2\<le>N\<and>f=inv__28  p__Inv2" apply fastforce done
have "(i=p__Inv2)\<or>(i~=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv2)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv2)"
  have "?P2 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_SendInvAckVsinv__28:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_SendInvAck  i)" and
a2: "(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__28  p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_SendInvAck  i" apply fastforce done
from a2 obtain p__Inv2 where a2:"p__Inv2\<le>N\<and>f=inv__28  p__Inv2" apply fastforce done
have "(i=p__Inv2)\<or>(i~=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv2)"
  have "?P3 s"
  apply (cut_tac a1 a2 b1, simp, rule_tac x="(neg (andForm (eqn (IVar (Para (Ident ''InvSet'') p__Inv2)) (Const true)) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const Inv))))" in exI, auto) done
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv2)"
  have "?P2 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_RecvInvAckVsinv__28:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_RecvInvAck  i)" and
a2: "(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__28  p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_RecvInvAck  i" apply fastforce done
from a2 obtain p__Inv2 where a2:"p__Inv2\<le>N\<and>f=inv__28  p__Inv2" apply fastforce done
have "(i=p__Inv2)\<or>(i~=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv2)"
  have "((formEval (eqn (IVar (Ident ''ExGntd'')) (Const true)) s))\<or>((formEval (neg (eqn (IVar (Ident ''ExGntd'')) (Const true))) s))" by auto
  moreover {
    assume c1: "((formEval (eqn (IVar (Ident ''ExGntd'')) (Const true)) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (neg (eqn (IVar (Ident ''ExGntd'')) (Const true))) s))"
    have "?P2 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  ultimately have "invHoldForRule s f r (invariants N)" by satx
}
moreover {
  assume b1: "(i~=p__Inv2)"
  have "((formEval (eqn (IVar (Ident ''ExGntd'')) (Const true)) s))\<or>((formEval (neg (eqn (IVar (Ident ''ExGntd'')) (Const true))) s))" by auto
  moreover {
    assume c1: "((formEval (eqn (IVar (Ident ''ExGntd'')) (Const true)) s))"
    have "?P1 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  moreover {
    assume c1: "((formEval (neg (eqn (IVar (Ident ''ExGntd'')) (Const true))) s))"
    have "?P2 s"
    proof(cut_tac a1 a2 b1 c1, auto) qed
    then have "invHoldForRule s f r (invariants N)" by auto
  }
  ultimately have "invHoldForRule s f r (invariants N)" by satx
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_SendGntSVsinv__28:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_SendGntS  i)" and
a2: "(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__28  p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_SendGntS  i" apply fastforce done
from a2 obtain p__Inv2 where a2:"p__Inv2\<le>N\<and>f=inv__28  p__Inv2" apply fastforce done
have "(i=p__Inv2)\<or>(i~=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv2)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv2)"
  have "?P2 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_SendGntEVsinv__28:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_SendGntE N i)" and
a2: "(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__28  p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_SendGntE N i" apply fastforce done
from a2 obtain p__Inv2 where a2:"p__Inv2\<le>N\<and>f=inv__28  p__Inv2" apply fastforce done
have "(i=p__Inv2)\<or>(i~=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv2)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv2)"
  have "?P3 s"
  apply (cut_tac a1 a2 b1, simp, rule_tac x="(neg (andForm (eqn (IVar (Para (Ident ''InvSet'') p__Inv2)) (Const true)) (eqn (IVar (Para (Ident ''ShrSet'') p__Inv2)) (Const false))))" in exI, auto) done
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_RecvGntSVsinv__28:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_RecvGntS  i)" and
a2: "(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__28  p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_RecvGntS  i" apply fastforce done
from a2 obtain p__Inv2 where a2:"p__Inv2\<le>N\<and>f=inv__28  p__Inv2" apply fastforce done
have "(i=p__Inv2)\<or>(i~=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv2)"
  have "?P3 s"
  apply (cut_tac a1 a2 b1, simp, rule_tac x="(neg (andForm (eqn (IVar (Ident ''ExGntd'')) (Const true)) (eqn (IVar (Field (Para (Ident ''Chan2'') p__Inv2) ''Cmd'')) (Const GntS))))" in exI, auto) done
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv2)"
  have "?P2 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_RecvGntEVsinv__28:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_RecvGntE  i)" and
a2: "(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__28  p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_RecvGntE  i" apply fastforce done
from a2 obtain p__Inv2 where a2:"p__Inv2\<le>N\<and>f=inv__28  p__Inv2" apply fastforce done
have "(i=p__Inv2)\<or>(i~=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv2)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i~=p__Inv2)"
  have "?P2 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_SendReqE__part__1Vsinv__28:
  assumes a1: "\<exists> i. i\<le>N\<and>r=n_SendReqE__part__1  i" and
  a2: "(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__28  p__Inv2)"
  shows "invHoldForRule s f r (invariants N)"
  apply (rule noEffectOnRule, cut_tac a1 a2, auto) done
  

lemma n_StoreVsinv__28:
  assumes a1: "\<exists> i d. i\<le>N\<and>d\<le>N\<and>r=n_Store  i d" and
  a2: "(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__28  p__Inv2)"
  shows "invHoldForRule s f r (invariants N)"
  apply (rule noEffectOnRule, cut_tac a1 a2, auto) done
  

lemma n_SendReqE__part__0Vsinv__28:
  assumes a1: "\<exists> i. i\<le>N\<and>r=n_SendReqE__part__0  i" and
  a2: "(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__28  p__Inv2)"
  shows "invHoldForRule s f r (invariants N)"
  apply (rule noEffectOnRule, cut_tac a1 a2, auto) done
  

lemma n_SendReqSVsinv__28:
  assumes a1: "\<exists> i. i\<le>N\<and>r=n_SendReqS  i" and
  a2: "(\<exists> p__Inv2. p__Inv2\<le>N\<and>f=inv__28  p__Inv2)"
  shows "invHoldForRule s f r (invariants N)"
  apply (rule noEffectOnRule, cut_tac a1 a2, auto) done
  
end
