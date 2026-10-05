(* ==========================================================================)
   abl_mixrational_wide.v — UpReqMixRationalProxy 二分收敛宽形独立闭合件
   使命：闭合 rp_bsearch 最小性收敛宽形 r ≤ t+(hi−lo)/2^fuel——宿主内注记
      （UpReqMixRationalProxy_R2.v:452-455 / R3:449-453）自书配方的独立
      定理化；前提方向经实测核定为 lo ≤ t（基例 hi ≤ t+(hi−lo) ⟺ lo ≤ t）。
      语句前缀 rpw_：全库 grep 防撞 0 命中。
   依赖清单：Stdlib QArith.QArith；S02_CauchyComplete（QleT'/Qle_to_QleT'/
      QleT'_to_Qle/qeq_imp_qle/qltT_0_2/qmult_ltT_0_compat）；
      UpReqMixRationalProxy_R2（rp_bsearch/rp_qpow/rp_qpow_pos/rp_qlt_eq_r）；
      UpReqMixRationalProxy_R3（双宿主同构副本：Require 不 Import，
      全资格名引用，零名冲突）。
   对标行：UpReqMixRationalProxy_R2.v 头注定案口径（Id 外层不可 rewrite
      边界的绕行法）与 :385/:130 同族先例；R3 §0/§3 rp_ 工具副本逐字
      同构移植源。
   构造性注记：零承认语句、零经典逻辑；语句面纯 Set（QleT'＝Id(Bool) 形，
      前提亦 QleT'）；证明体内 Qle/field 旁证属 Prop 内部账、不入语句面
      （R2:385/:130 同族先例）。归纳在 Qle 内部层进行、闭合一次
      Qle_to_QleT'，绕开 Id 外层不可 rewrite 边界。
   编译配方：rocq c -native-compiler no（-Q 世界根 ""）单发编译；验证＝
      EXIT=0＋日志零真错＋尾 Print Assumptions 全 Closed＋.vo 文件头
      魔数 436f712100015ff4 校验。
   查重登记：顶层名 2 枚（rpw_bsearch_min/rpw_bsearch_min_r3）全 rpw_
      新前缀零撞零别名转发；R3 副本与 R2 宿主逐字同构、零重复零遗漏；
      宿主件零字节不动、零重编。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith.
Require Import S02_CauchyComplete.
Require Import UpReqMixRationalProxy_R2.
(* R3 双宿主同构副本（Require 不 Import，全资格名引用，零名冲突） *)
Require UpReqMixRationalProxy_R3.

(* ============ 主件：二分最小性收敛宽形（R2 宿主） ============ *)
(* r ≤ t + (hi−lo)/2^fuel，前提 lo ≤ t（QleT' 纯 Set 形）。
   证明：fuel 结构归纳；两支区间宽各减半、与走支无关，故双支均无条件闭合；
   field 恒等式旁证 rp_qpow (2#1) f ≠ 0 由 rp_qpow_pos 正性件桥入
   （rp_qlt_eq_r 换元 + Qlt_irrefl 爆破），非承认。 *)
Lemma rpw_bsearch_min : forall (t : Q) (fuel : nat) (lo hi : Q),
  QleT' lo t ->
  QleT' (rp_bsearch t fuel lo hi) (t + (hi - lo) / rp_qpow (2#1) fuel).
Proof.
  intros t fuel.
  induction fuel as [| f IHf]; intros lo hi Htl.
  - (* 基例 fuel=0：r=hi，归约账 hi ≤ t+(hi−lo)/1 ⟸ lo ≤ t *)
    apply Qle_to_QleT'.
    assert (Hle : Qle lo t) by (apply QleT'_to_Qle; exact Htl).
    assert (Hp : (rp_qpow (2#1) 0 == 1#1)%Q) by reflexivity.
    rewrite Hp.
    assert (Hd : Qle 0 (t - lo)).
    { apply (Qle_trans 0 (lo + -lo) (t - lo)).
      - apply (qeq_imp_qle _ _). field.
      - apply (Qplus_le_compat lo t (-lo) (-lo)); [exact Hle | apply Qle_refl]. }
    apply (Qle_trans hi (hi + (t - lo)) (t + (hi - lo) / (1#1))).
    + apply (Qle_trans hi (hi + 0) (hi + (t - lo))).
      * apply (qeq_imp_qle _ _). field.
      * apply (Qplus_le_compat hi hi 0 (t - lo)); [apply Qle_refl | exact Hd].
    + apply (qeq_imp_qle _ _). field.
  - (* 归纳步 fuel=S f：双支均以 IHf+field 恒等式闭合 *)
    apply Qle_to_QleT'.
    simpl.
    destruct (Qle_bool t ((lo + hi) / 2)) eqn:E.
    + (* 真：走左支，r=bsearch t f lo mid，lo 不变 *)
      assert (Eqt : (t + (hi - lo) / ((2#1) * rp_qpow (2#1) f)
                  == t + ((lo + hi) / 2 - lo) / rp_qpow (2#1) f)%Q)
        by (field; intro Hzz; apply (Qlt_irrefl 0%Q); apply QltT_to_Qlt;
            exact (rp_qlt_eq_r 0%Q (rp_qpow (2#1) f) 0%Q Hzz
                     (rp_qpow_pos (2#1) f qltT_0_2))).
      rewrite Eqt.
      exact (QleT'_to_Qle _ _ (IHf lo ((lo + hi) / 2) Htl)).
    + (* 假：走右支，r=bsearch t f mid hi；由支判定 E（S02 Qle_bool 形，
         t ≤ mid 不成立）补 mid ≤ t，代入 IHf 右支实例。
         注意：S02 自定义 Qle_bool（Qcompare 反映形）遮蔽 stdlib 版，
         stdlib Qle_bool_iff 异名不通用——走 S02 自家桥 Qle_to_QleT'
         + Bool 等式 rewrite 爆 Id（Id 外层无 setoid 注册，Bool 等式
         项级替换不在禁令内）。 *)
      assert (Hmt : Qle ((lo + hi) / 2) t).
      { apply Qlt_le_weak. apply Qnot_le_lt. intro Hq.
        apply (Qle_to_QleT' t ((lo + hi) / 2)) in Hq.
        unfold QleT' in Hq. rewrite E in Hq. inversion Hq. }
      assert (Eqf : (t + (hi - lo) / ((2#1) * rp_qpow (2#1) f)
                  == t + (hi - (lo + hi) / 2) / rp_qpow (2#1) f)%Q)
        by (field; intro Hzz; apply (Qlt_irrefl 0%Q); apply QltT_to_Qlt;
            exact (rp_qlt_eq_r 0%Q (rp_qpow (2#1) f) 0%Q Hzz
                     (rp_qpow_pos (2#1) f qltT_0_2))).
      rewrite Eqf.
      exact (QleT'_to_Qle _ _
               (IHf ((lo + hi) / 2) hi (Qle_to_QleT' _ _ Hmt))).
Qed.

(* ============ R3 双宿主同构副本（逐字同构移植：R3 §0/§3 rp_ 工具副本与
   R2 同文同定义；全资格名引用） ============ *)
Lemma rpw_bsearch_min_r3 : forall (t : Q) (fuel : nat) (lo hi : Q),
  QleT' lo t ->
  QleT' (UpReqMixRationalProxy_R3.rp_bsearch t fuel lo hi)
        (t + (hi - lo) / UpReqMixRationalProxy_R3.rp_qpow (2#1) fuel).
Proof.
  intros t fuel.
  induction fuel as [| f IHf]; intros lo hi Htl.
  - (* 基例 fuel=0 *)
    apply Qle_to_QleT'.
    assert (Hle : Qle lo t) by (apply QleT'_to_Qle; exact Htl).
    assert (Hp : (UpReqMixRationalProxy_R3.rp_qpow (2#1) 0 == 1#1)%Q)
      by reflexivity.
    rewrite Hp.
    assert (Hd : Qle 0 (t - lo)).
    { apply (Qle_trans 0 (lo + -lo) (t - lo)).
      - apply (qeq_imp_qle _ _). field.
      - apply (Qplus_le_compat lo t (-lo) (-lo)); [exact Hle | apply Qle_refl]. }
    apply (Qle_trans hi (hi + (t - lo)) (t + (hi - lo) / (1#1))).
    + apply (Qle_trans hi (hi + 0) (hi + (t - lo))).
      * apply (qeq_imp_qle _ _). field.
      * apply (Qplus_le_compat hi hi 0 (t - lo)); [apply Qle_refl | exact Hd].
    + apply (qeq_imp_qle _ _). field.
  - (* 归纳步 fuel=S f *)
    apply Qle_to_QleT'.
    simpl.
    destruct (Qle_bool t ((lo + hi) / 2)) eqn:E.
    + assert (Eqt : (t + (hi - lo) / ((2#1) * UpReqMixRationalProxy_R3.rp_qpow (2#1) f)
                  == t + ((lo + hi) / 2 - lo)
                     / UpReqMixRationalProxy_R3.rp_qpow (2#1) f)%Q)
        by (field; intro Hzz; apply (Qlt_irrefl 0%Q); apply QltT_to_Qlt;
            exact (UpReqMixRationalProxy_R3.rp_qlt_eq_r 0%Q
                     (UpReqMixRationalProxy_R3.rp_qpow (2#1) f) 0%Q Hzz
                     (UpReqMixRationalProxy_R3.rp_qpow_pos (2#1) f qltT_0_2))).
      rewrite Eqt.
      exact (QleT'_to_Qle _ _ (IHf lo ((lo + hi) / 2) Htl)).
    + assert (Hmt : Qle ((lo + hi) / 2) t).
      { apply Qlt_le_weak. apply Qnot_le_lt. intro Hq.
        apply (Qle_to_QleT' t ((lo + hi) / 2)) in Hq.
        unfold QleT' in Hq. rewrite E in Hq. inversion Hq. }
      assert (Eqf : (t + (hi - lo) / ((2#1) * UpReqMixRationalProxy_R3.rp_qpow (2#1) f)
                  == t + (hi - (lo + hi) / 2)
                     / UpReqMixRationalProxy_R3.rp_qpow (2#1) f)%Q)
        by (field; intro Hzz; apply (Qlt_irrefl 0%Q); apply QltT_to_Qlt;
            exact (UpReqMixRationalProxy_R3.rp_qlt_eq_r 0%Q
                     (UpReqMixRationalProxy_R3.rp_qpow (2#1) f) 0%Q Hzz
                     (UpReqMixRationalProxy_R3.rp_qpow_pos (2#1) f qltT_0_2))).
      rewrite Eqf.
      exact (QleT'_to_Qle _ _
               (IHf ((lo + hi) / 2) hi (Qle_to_QleT' _ _ Hmt))).
Qed.

(* ============ 取证段 ============ *)
Print Assumptions rpw_bsearch_min.
Print Assumptions rpw_bsearch_min_r3.
