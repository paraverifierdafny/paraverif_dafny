(*  Title:      HOL/Auth/n_mutualExOnI_on_inis.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_mutualExOnI Protocol Case Study*} 

theory n_mutualExOnI_on_inis imports n_mutualExOnI_on_ini
begin
lemma on_inis:
  assumes b1: "f \<in> (invariants N)" and b2: "ini \<in> {andList (allInitSpecs N)}" and b3: "formEval ini s"
  shows "formEval f s"
  proof -
  have c1: "(\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__1  p__Inv0 p__Inv1)\<or>
    (\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__2  p__Inv0 p__Inv1)\<or>
    (\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__3  p__Inv0 p__Inv1)\<or>
    (\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__4  p__Inv0 p__Inv1)"
  apply (cut_tac b1, simp) done
    moreover {
      assume d1: "(\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__1  p__Inv0 p__Inv1)"
      have "formEval f s"
      apply (rule iniImply_inv__1)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__2  p__Inv0 p__Inv1)"
      have "formEval f s"
      apply (rule iniImply_inv__2)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__3  p__Inv0 p__Inv1)"
      have "formEval f s"
      apply (rule iniImply_inv__3)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

    moreover {
      assume d1: "(\<exists> p__Inv0 p__Inv1. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv0~=p__Inv1\<and>f=inv__4  p__Inv0 p__Inv1)"
      have "formEval f s"
      apply (rule iniImply_inv__4)
      apply (cut_tac d1, assumption)
      apply (cut_tac b2 b3, blast) done
    }

  ultimately show "formEval f s"
  by satx
qed

end
