(* ============================================================
   模块名: piu_zz_constants
   数学使命: Zeilberger–Zudilin 2020 π 无理性测度上界路线
     (arXiv:1912.06345v2, Moscow J. Comb. Number Th. 9 (2020) 407-419)
     全部关键常数的精确有理数 (Q) 固化, 以及 Giraudin 2026
     (arXiv:2609.37459v2) 闭式律的树内可复算形:
     ① σ/τ/s/Λ 常数面与 μ = 1 + σ/τ 闭式 (ZZ「World record」节);
     ② Giraudin 律有理骨架 R_lcm/c_P/c_2/Λ/μ 的 Defined 计算形
       (对数型输入 W, log 2 以显式 Q 参数进入——诚实接口);
     ③ P < 100 的 16 个 Machin 容许配置 (P, w) 的精确整数恒等式;
     ④ (2,2,3) 配置 μ = 7.103205334137… 对拍与 (1857,1857,2785)
       (Bai 点) 系数恒等式组;
     ⑤ 三条 p-adic 引理语句面记录 (仅语句面, 证明属后续整理件).
   依赖: 仅 Stdlib (ZArith, QArith, QArith.Qabs); 零树内 Require.
   对标: [ZZ2020] arXiv:1912.06345v2; [G26] arXiv:2609.37459v2 §6/§9.
   构造性注记: 零 Axiom/Admitted/Parameter/Conjecture/Abort; 一切
     有名语句 Set 承载 (布尔载体 zzZeqT/zzNatEqT/zzQeqT/zzQltT/
     zzQleT/zzQband : Set, 真值分支 unit, 假值分支 Empty_set),
     全文件无 Prop 承载语句; 一切证明由封闭项 vm_compute 闭合.
     数值为文献十进制值的精确 Q 截断 (位数见各定义处注), 非
     超越值本身; 不等式型结论均以显式容差带陈述, 容差覆盖输入
     截断误差. [G26] Result J («7.101862832356 is the floor of the
     whole method») 系原文自标 CONJECTURE, 本文件不作定理断言,
     仅证明 Bai 点记录值小于 (2,2,3) 值这一方向性比较.
   编译配方: rocq c -native-compiler no -q -Q . "" piu_zz_constants.v
     (Rocq 9.1.0, cpu_guard 包裹, env.sh 后 unset COQLIB ROCQLIB)
   ============================================================ *)

From Stdlib Require Import ZArith QArith.QArith QArith.Qabs.
Open Scope Q_scope.

(* ============================================================ *)
(* §0 Set 承载布尔载体 (自足定义, 命名加 zz 前缀避免同层撞名)      *)
(* ============================================================ *)

Definition zzZeqT (n m : Z) : Set :=
  match Z.eqb n m with true => unit | false => Empty_set end.

Definition zzNatEqT (n m : nat) : Set :=
  match Nat.eqb n m with true => unit | false => Empty_set end.

Definition zzQeqT (x y : Q) : Set :=
  match Qeq_bool x y with true => unit | false => Empty_set end.

(* Q 严格序: 交叉相乘形 (对非规范分母同样成立) *)
Definition zzQlt_bool (x y : Q) : bool := (Qnum x * QDen y <? Qnum y * QDen x)%Z.

Definition zzQltT (x y : Q) : Set :=
  match zzQlt_bool x y with true => unit | false => Empty_set end.

Definition zzQleT (x y : Q) : Set :=
  match Qle_bool x y with true => unit | false => Empty_set end.

(* 区间承载: lo ≤ x ≤ hi *)
Definition zzQband (x lo hi : Q) : Set :=
  match andb (Qle_bool lo x) (Qle_bool x hi) with
  | true => unit | false => Empty_set
  end.

Definition zzQmax (x y : Q) : Q := if Qle_bool x y then y else x.

Definition zzQ_of_Z (n : Z) : Q := (n # 1).

(* ============================================================ *)
(* §1 文献常数面 (十进制截断的精确 Q 形)                           *)
(* ============================================================ *)

(* σ = 11.61389004533104820528984629866735…  [ZZ2020 World record 第二式] 32 位截断 *)
Definition piu_zzc_sigma : Q :=
  (1161389004533104820528984629866735 # 100000000000000000000000000000000).

(* τ = 1.90291648559998216823282018815429…  [ZZ2020 World record 第一式取绝对值] 32 位截断 *)
Definition piu_zzc_tau : Q :=
  (190291648559998216823282018815429 # 100000000000000000000000000000000).

(* s = 3.52477292396528388…  [G26] Thm 2 标定值 s = 3.524772924 (鞍点 min-max 衰减率) 的高精度延拓, 17 位截断 *)
Definition piu_zzc_s : Q := (352477292396528388 # 100000000000000000).

(* Λ(2,2,3) = 1.62185643836530171941…  [G26] §6 标定表行 1, 20 位截断 *)
Definition piu_zzc_Lambda_223 : Q := (162185643836530171941 # 100000000000000000000).

(* μ(2,2,3) = 7.1032053341370017275057734228103…  [ZZ2020] 公布值, 31 位截断 (对拍基准) *)
Definition piu_zzc_mu_223_lit : Q := (71032053341370017275057734228103 # 10000000000000000000000000000000).

(* μ(Bai) = 7.1018628323563507  [G26] §6 标定表行 3, 16 位 *)
Definition piu_zzc_mu_bai_lit : Q := (71018628323563507 # 10000000000000000).

(* μ(3,3,5) = 7.6063085207111912  [G26] §6 标定表行 2 (Salikhov 路线), 16 位 *)
Definition piu_zzc_mu_335_lit : Q := (76063085207111912 # 10000000000000000).

(* W = 0.645275610234…  [G26] (2,2,3) 窗常数 = π/(2√3) − log(3√3/4), 12 位截断 *)
Definition piu_zzc_W_223 : Q := (645275610234 # 1000000000000).

(* W_Bai = 601.2828866806  [G26] Bai 点窗常数 (文献 10 位记录输入) *)
Definition piu_zzc_W_bai : Q := (6012828866806 # 10000000000).

(* log 2 = 0.6931471805599453…  16 位截断 (闭式律对数输入) *)
Definition piu_zzc_ln2 : Q := (6931471805599453 # 10000000000000000).

(* Λ(Bai) = 1503.8827864689270  [G26] §6 标定表行 3, 13 位 (对拍基准) *)
Definition piu_zzc_Lambda_bai_lit : Q := (15038827864689270 # 10000000000000).

(* 鞍点与判别式上游量 ([ZZ2020] Prop. 2 式 (18) 整系数三次式之根, 记录面) *)
Definition piu_zzc_N3 : Q := (2185169139621956 # 100000000000).
Definition piu_zzc_y3 : Q := (6633950152462140 # 100000000000000).
Definition piu_zzc_absN1 : Q := (29458495928116876 # 1000000000000000000).

(* 工作口径粗值 (文献早期公布舍入/截断形) *)
Definition piu_zzc_sigma_coarse : Q := (116139 # 10000).
Definition piu_zzc_tau_coarse : Q := (19029 # 10000).
Definition piu_zzc_s_coarse : Q := (3525 # 1000).
Definition piu_zzc_Lambda_coarse : Q := (1621 # 1000).

(* ============================================================ *)
(* §2 导出闭式形                                                  *)
(* ============================================================ *)

(* ZZ 闭式: μ = 1 + σ/τ (定义即计算形; 与 Giraudin 律在 (2,2,3) 的
   一致性由 §6 piu_zzc_giraudin_matches_zz_223 以容差带复核) *)
Definition piu_zzc_mu_223 : Q := (1 # 1) + piu_zzc_sigma / piu_zzc_tau.

(* ZZ 值 7.103205334137 的 12 位十进制下截断与上取整 *)
Definition piu_zzc_mu_zz_lower : Q := (7103205334137 # 1000000000000).
Definition piu_zzc_mu_zz_upper : Q := (7103205334138 # 1000000000000).

(* 鞍点指标 S = max_i log|g(ζ_i)| = log N_3: 由 σ = S + Λ 反解 *)
Definition piu_zzc_S_223 : Q := piu_zzc_sigma - piu_zzc_Lambda_223.

(* (5,1+2i) 配置: N(P+w) 与 N(P−w), w = 1+2i, P = 5 *)
Definition piu_zzc_np_w : Z := ((5 + 1) * (5 + 1) + 2 * 2)%Z.
Definition piu_zzc_nm_w : Z := ((5 - 1) * (5 - 1) + (0 - 2) * (0 - 2))%Z.

(* 2-adic 赋值 (正 part 递归; 负数与非正输入记 0) *)
Fixpoint zz_v2_pos (p : positive) : nat :=
  match p with
  | xO q => S (zz_v2_pos q)
  | _ => 0
  end.

Definition zz_v2 (n : Z) : nat :=
  match n with Zpos p => zz_v2_pos p | _ => 0 end.

(* λ± = v_2(N(P±w))/2: (5,1+2i) 配置给 λ₊ = 3/2, λ₋ = 1 *)
Definition piu_zzc_lam_p : Q := zzQ_of_Z (Z.of_nat (zz_v2 piu_zzc_np_w)) * (1 # 2).
Definition piu_zzc_lam_m : Q := zzQ_of_Z (Z.of_nat (zz_v2 piu_zzc_nm_w)) * (1 # 2).

(* ============================================================ *)
(* §3 Giraudin 闭式律有理骨架 (Defined 计算形, Q 全程)             *)
(*    律本体 [G26] §6: Λ = R_lcm − W − c_2·log 2 + c_P·log P     *)
(*    − Σ_q c_q·log q;  μ = 1 + (S+Λ)/(s−Λ).                    *)
(*    对数型输入 W, log 2, log P 与鞍点量 S, s 及高斯素数特征     *)
(*    λ± 以显式 Q 参数进入——可超越量不作隐藏公理, 诚实接口.       *)
(* ============================================================ *)

(* lcm 窗半径 R_lcm = max(b, a0 + 4a1 − 2b)   [G26] Thm 3 *)
Definition zz_R_lcm (a0 a1 b : Z) : Z := Z.max b (a0 + 4 * a1 - 2 * b)%Z.

(* P-ADIC 档 c_P = max(0, 2b − a0 − 2a1)   [G26] Thm 3 *)
Definition zz_cP (a0 a1 b : Z) : Z := Z.max 0 (2 * b - a0 - 2 * a1)%Z.

(* 2-adic 节省 c_2 (一般形, λ± 为参数)   [G26] Thm 3:
   b ≤ 2a1 时 c_2 = 2(λ₊+λ₋)a1 − (1+max(λ₊,λ₋,1))b;
   b > 2a1 时 c_2 = 4λ₋a1 − (1+λ₋)b. *)
Definition zz_c2g (lp lm : Q) (a1 b : Z) : Q :=
  if Z.leb b (2 * a1)%Z
  then (2 # 1) * (lp + lm) * zzQ_of_Z a1
       - ((1 # 1) + zzQmax lp (zzQmax lm (1 # 1))) * zzQ_of_Z b
  else (4 # 1) * lm * zzQ_of_Z a1 - ((1 # 1) + lm) * zzQ_of_Z b.

(* (5,1+2i) 配置特化 (λ₊ = 3/2, λ₋ = 1): c_2 = 5a1 − (5/2)b (b ≤ 2a1) *)
Definition zz_c2_51 (a1 b : Z) : Q := zz_c2g (3 # 2) (1 # 1) a1 b.

(* 组合常数 Λ (无奇 q 支配置, c_q = 0) *)
Definition zz_Lambda (a0 a1 b : Z) (lp lm Wx l2 lP : Q) : Q :=
  zzQ_of_Z (zz_R_lcm a0 a1 b) - Wx - zz_c2g lp lm a1 b * l2
  + zzQ_of_Z (zz_cP a0 a1 b) * lP.

(* Giraudin 闭式律: μ = 1 + (S+Λ)/(s−Λ) *)
Definition zz_mu_closed (a0 a1 b : Z) (Sx sx Wx l2 lP lp lm : Q) : Q :=
  let L := zz_Lambda a0 a1 b lp lm Wx l2 lP in
  (1 # 1) + (Sx + L) / (sx - L).

(* 律在 (2,2,3) 的实例 (文献输入) 与 Bai 点 Λ 复算形 *)
Definition piu_zzc_mu_g_223 : Q :=
  zz_mu_closed 2 2 3 piu_zzc_S_223 piu_zzc_s piu_zzc_W_223 piu_zzc_ln2
               (0 # 1) (3 # 2) (1 # 1).

Definition piu_zzc_Lambda_223_rec : Q :=
  zzQ_of_Z (zz_R_lcm 2 2 3) - piu_zzc_W_223 - zz_c2_51 2 3 * piu_zzc_ln2
  + zzQ_of_Z (zz_cP 2 2 3) * (0 # 1).

Definition piu_zzc_Lambda_bai_rec : Q :=
  zzQ_of_Z (zz_R_lcm 1857 1857 2785) - piu_zzc_W_bai
  - zz_c2_51 1857 2785 * piu_zzc_ln2
  + zzQ_of_Z (zz_cP 1857 1857 2785) * (0 # 1).

(* ============================================================ *)
(* §4 P < 100 的 16 个 Machin 容许配置 (P, u, v), w = u+v·i       *)
(*    [G26] §9 表; 容许条件 u²+(v+P)² = 2P², 本原解 (gcd(P,u,v)=1) *)
(* ============================================================ *)

Definition piu_zzc_cfg01 : Z * Z * Z := (5%Z, 1%Z, 2%Z).
Definition piu_zzc_cfg02 : Z * Z * Z := (13%Z, 7%Z, 4%Z).
Definition piu_zzc_cfg03 : Z * Z * Z := (17%Z, 7%Z, 6%Z).
Definition piu_zzc_cfg04 : Z * Z * Z := (25%Z, 17%Z, 6%Z).
Definition piu_zzc_cfg05 : Z * Z * Z := (29%Z, 1%Z, 12%Z).
Definition piu_zzc_cfg06 : Z * Z * Z := (37%Z, 23%Z, 10%Z).
Definition piu_zzc_cfg07 : Z * Z * Z := (41%Z, 31%Z, 8%Z).
Definition piu_zzc_cfg08 : Z * Z * Z := (53%Z, 17%Z, 20%Z).
Definition piu_zzc_cfg09 : Z * Z * Z := (61%Z, 49%Z, 10%Z).
Definition piu_zzc_cfg10 : Z * Z * Z := (65%Z, 23%Z, 24%Z).
Definition piu_zzc_cfg11 : Z * Z * Z := (65%Z, 47%Z, 14%Z).
Definition piu_zzc_cfg12 : Z * Z * Z := (73%Z, 7%Z, 30%Z).
Definition piu_zzc_cfg13 : Z * Z * Z := (85%Z, 41%Z, 28%Z).
Definition piu_zzc_cfg14 : Z * Z * Z := (85%Z, 71%Z, 12%Z).
Definition piu_zzc_cfg15 : Z * Z * Z := (89%Z, 41%Z, 30%Z).
Definition piu_zzc_cfg16 : Z * Z * Z := (97%Z, 7%Z, 40%Z).

Definition piu_zzc_machin_b (c : Z * Z * Z) : bool :=
  let '(P, u, v) := c in Z.eqb (u * u + (v + P) * (v + P))%Z (2 * (P * P))%Z.

Definition piu_zzc_prim_b (c : Z * Z * Z) : bool :=
  let '(P, u, v) := c in Z.eqb (Z.gcd P (Z.gcd u v)) 1%Z.

(* ============================================================ *)
(* §5 (5,1+2i) 配置的 λ± 与 content                                *)
(* ============================================================ *)

Lemma piu_zzc_np_w_val : zzZeqT piu_zzc_np_w 40%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_nm_w_val : zzZeqT piu_zzc_nm_w 20%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_lam_p_val : zzQeqT piu_zzc_lam_p (3 # 2).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_lam_m_val : zzQeqT piu_zzc_lam_m (1 # 1).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_content_p_plus : zzZeqT (Z.gcd (5 + 1)%Z 2%Z) 2%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_content_p_minus : zzZeqT (Z.gcd (5 - 1)%Z 2%Z) 2%Z.
Proof. vm_compute. exact tt. Qed.

(* ============================================================ *)
(* §6 验证定理面                                                   *)
(* ============================================================ *)

(* —— 6.1 粗值与全精度形的一致 (舍入/截断半径内) —— *)

Lemma piu_zzc_sigma_coarse_band :
  zzQband (Qabs (piu_zzc_sigma - piu_zzc_sigma_coarse)) (0 # 1) (1 # 20000).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_tau_coarse_band :
  zzQband (Qabs (piu_zzc_tau - piu_zzc_tau_coarse)) (0 # 1) (1 # 20000).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_s_coarse_band :
  zzQband (Qabs (piu_zzc_s - piu_zzc_s_coarse)) (0 # 1) (1 # 2000).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_Lambda_coarse_band :
  zzQband (Qabs (piu_zzc_Lambda_223 - piu_zzc_Lambda_coarse)) (0 # 1) (1 # 1000).
Proof. vm_compute. exact tt. Qed.

(* —— 6.2 ZZ 闭式 μ = 1 + σ/τ 的 26 位逐位复核与 12 位夹逼 —— *)
(* 复核值: 1+σ/τ = 7.1032053341370017275057734 22810327…,          *)
(* 前 26 位小数与 [ZZ2020] 公布值 7.1032053341370017275057734228103… *)
(* 逐位一致 (第 27 位起差异 ≤ 3.8e−32, 系 σ/τ 截断传播).            *)

Lemma piu_zzc_mu223_floor26 :
  zzZeqT (Z.div (Qnum piu_zzc_mu_223 * 100000000000000000000000000)%Z
                 (Z.pos (Qden piu_zzc_mu_223)))
         710320533413700172750577342%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_mu223_lower_bound : zzQltT piu_zzc_mu_zz_lower piu_zzc_mu_223.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_mu223_upper_bound : zzQltT piu_zzc_mu_223 piu_zzc_mu_zz_upper.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_mu223_matches_lit :
  zzQband (Qabs (piu_zzc_mu_223 - piu_zzc_mu_223_lit)) (0 # 1)
          (1 # 1000000000000000000000000000000).
Proof. vm_compute. exact tt. Qed.

(* —— 6.3 (2,2,3) 有理骨架 —— *)

Lemma piu_zzc_R_lcm_223 : zzZeqT (zz_R_lcm 2 2 3) 4%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_cP_223 : zzZeqT (zz_cP 2 2 3) 0%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_c2_223 : zzQeqT (zz_c2_51 2 3) (5 # 2).
Proof. vm_compute. exact tt. Qed.

(* 截断输入 (W 12 位, log 2 16 位) 复算 Λ 与 20 位记录值之差在 1e−12 内 *)
Lemma piu_zzc_Lambda_223_rec_band :
  zzQband (Qabs (piu_zzc_Lambda_223_rec - piu_zzc_Lambda_223)) (0 # 1)
          (1 # 1000000000000).
Proof. vm_compute. exact tt. Qed.

(* —— 6.4 Bai 点 (1857,1857,2785) 系数恒等式组 —— *)
(* 顶点 Q = 2a/(3a−2b) = 3714; R_lcm = 3715; c_P = 0;              *)
(* c_2 = 4645/2 = 5a1 − (5/2)b; b/a1 = 3/2 − 1/3714.               *)

Lemma piu_zzc_bai_vertex :
  zzQeqT (zzQ_of_Z (2 * 1857)%Z / zzQ_of_Z (3 * 1857 - 2 * 2785)%Z) (3714 # 1).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_R_lcm_bai : zzZeqT (zz_R_lcm 1857 1857 2785) 3715%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_cP_bai : zzZeqT (zz_cP 1857 1857 2785) 0%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_c2_bai : zzQeqT (zz_c2_51 1857 2785) (4645 # 2).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_bai_ratio : zzQeqT (2785 # 1857) ((3 # 2) - (1 # 3714)).
Proof. vm_compute. exact tt. Qed.

(* 截断输入复算 Λ(Bai) 的 13 位小数逐位复核:                        *)
(* 3715 − 601.2828866806 − (4645/2)·log 2 = 1503.88278646892704…,  *)
(* floor(·10^13) = 15038827864689270 与 13 位记录值一致.            *)
Lemma piu_zzc_Lambda_bai_rec_floor13 :
  zzZeqT (Z.div (Qnum piu_zzc_Lambda_bai_rec * 10000000000000)%Z
                 (Z.pos (Qden piu_zzc_Lambda_bai_rec)))
         15038827864689270%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_Lambda_bai_rec_band :
  zzQband (Qabs (piu_zzc_Lambda_bai_rec - piu_zzc_Lambda_bai_lit)) (0 # 1)
          (1 # 10000000000000).
Proof. vm_compute. exact tt. Qed.

(* 方向性比较: Bai 记录值 < (2,2,3) 值. [G26] Result J 将 7.101862832356 *)
(* 为全方法下界标为 CONJECTURE, 此处不断言该猜想, 仅证方向.           *)
Lemma piu_zzc_bai_below_zz : zzQltT piu_zzc_mu_bai_lit piu_zzc_mu_223.
Proof. vm_compute. exact tt. Qed.

(* —— 6.5 Giraudin 律与 ZZ 闭式在 (2,2,3) 的交叉复核 —— *)
(* 截断输入传播误差 ≤ 3.2e−12 (W 12 位为主项), 容差 1e−11.           *)
Lemma piu_zzc_giraudin_matches_zz_223 :
  zzQband (Qabs (piu_zzc_mu_g_223 - piu_zzc_mu_223)) (0 # 1)
          (1 # 100000000000).
Proof. vm_compute. exact tt. Qed.

(* —— 6.6 16 配置逐配置精确恒等式 —— *)

Lemma piu_zzc_machin_01 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg01 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg01 in (2 * (P * P))%Z).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_prim_01 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg01 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_machin_02 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg02 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg02 in (2 * (P * P))%Z).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_prim_02 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg02 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_machin_03 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg03 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg03 in (2 * (P * P))%Z).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_prim_03 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg03 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_machin_04 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg04 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg04 in (2 * (P * P))%Z).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_prim_04 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg04 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_machin_05 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg05 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg05 in (2 * (P * P))%Z).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_prim_05 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg05 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_machin_06 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg06 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg06 in (2 * (P * P))%Z).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_prim_06 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg06 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_machin_07 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg07 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg07 in (2 * (P * P))%Z).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_prim_07 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg07 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_machin_08 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg08 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg08 in (2 * (P * P))%Z).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_prim_08 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg08 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_machin_09 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg09 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg09 in (2 * (P * P))%Z).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_prim_09 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg09 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_machin_10 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg10 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg10 in (2 * (P * P))%Z).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_prim_10 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg10 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_machin_11 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg11 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg11 in (2 * (P * P))%Z).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_prim_11 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg11 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_machin_12 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg12 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg12 in (2 * (P * P))%Z).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_prim_12 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg12 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_machin_13 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg13 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg13 in (2 * (P * P))%Z).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_prim_13 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg13 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_machin_14 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg14 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg14 in (2 * (P * P))%Z).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_prim_14 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg14 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_machin_15 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg15 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg15 in (2 * (P * P))%Z).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_prim_15 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg15 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_machin_16 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg16 in (u * u + (v + P) * (v + P))%Z)
         (let '(P, u, v) := piu_zzc_cfg16 in (2 * (P * P))%Z).
Proof. vm_compute. exact tt. Qed.

Lemma piu_zzc_prim_16 :
  zzZeqT (let '(P, u, v) := piu_zzc_cfg16 in Z.gcd P (Z.gcd u v)) 1%Z.
Proof. vm_compute. exact tt. Qed.

(* ============================================================ *)
(* §7 三条 p-adic 引理语句面记录                                    *)
(*    ([ZZ2020] Lemma 1 / Lemma 2 / Lemma 3; 仅语句面, 证明属       *)
(*    后续整理件, 本文件不开证. Lemma 2 必须采用 v2 修正版语句——    *)
(*    v1 关于 T(m) 的整性断言已被作者撤回, 不可采用.)               *)
(* ------------------------------------------------------------ *)
(* 记号. I_{A,B}(n) 的部分分式:                                    *)
(*   R(x) = 5x^{2n}(x^4+6x^2+25)^{2n} / ((5+x)^{3n+1}(5−x)^{3n+1}) *)
(*          = P(x) + Σ_{j=0}^{3n} ( A_j/(5+x)^{j+1} + A_j/(5−x)^{j+1} ), *)
(* 其中 P ∈ Z[x²] 次数 4n−2, R(−x) = R(x). 记 {x} = x − ⌊x⌋.        *)
(*                                                                *)
(* 引理 A ([ZZ2020] Lemma 1, 整性下界). 对 j = 0, …, 3n:            *)
(*        2^{−⌊(5n+3j)/2⌋+1} · 5^{−j} · A_j ∈ Z.                   *)
(*    (证明工具: 算子 D_m : f ↦ f^{(m)}(−5)/m!, Leibniz 展开给      *)
(*    A_j = Σ_{m ∈ M_j} (−1)^{m1+…+m5} T(m) 2^{4n−1+j+m1}          *)
(*    (1−i)^{−m4} (1+i)^{−m5} 5^j (2+i)^{m2+m5} (2−i)^{m3+m4},     *)
(*    M_j = {m0+…+m5 = 3n−j, m1..5 ≤ 2n}, 关键步 (1±i)² = ±2i.)     *)
(*                                                                *)
(* 引理 B ([ZZ2020] Lemma 2, v2 修正版). 对                         *)
(*        P_n = { p > max{5, √(3n)} : 1/2 ≤ {n/p} < 2/3 }          *)
(*    中任一素数 p 及 j ∈ {−4n+1, −4n+2, …, 3n}: 若 p ∣ j, 则       *)
(*        A_j ≡ 0 (mod p)   (等价地 p ∣ 10^{−j} A_j).               *)
(*                                                                *)
(* 引理 C ([ZZ2020] Lemma 3, 清整除法). 记 Φ_n = ∏_{p ∈ P_n} p,     *)
(* L_n = lcm(1, 2, …, 4n) / Φ_n ∈ Z, 则                            *)
(*        L_n · 10^{−j} A_j / j ∈ Z   (j ∈ {−4n, …, 3n}, j ≠ 0),    *)
(*        Φ_n^{−1} · A_0 ∈ Z.                                      *)
(*    附 (式 (10)): lim_{n→∞} (log Φ_n)/n                           *)
(*       = π/(2√3) − log(3√3/4) = 0.64527561…  (= piu_zzc_W_223 之常数). *)
(* ============================================================ *)

(* ============================================================ *)
(* §8 vm_compute 取值检查 (编译日志出口, 供逐位对表)                *)
(* ============================================================ *)

Eval vm_compute in piu_zzc_mu_223.
Eval vm_compute in piu_zzc_Lambda_223_rec.
Eval vm_compute in piu_zzc_Lambda_bai_rec.
Eval vm_compute in piu_zzc_mu_g_223.
Eval vm_compute in piu_zzc_lam_p.
Eval vm_compute in piu_zzc_lam_m.
Eval vm_compute in (piu_zzc_machin_b piu_zzc_cfg01, piu_zzc_machin_b piu_zzc_cfg02,
  piu_zzc_machin_b piu_zzc_cfg03, piu_zzc_machin_b piu_zzc_cfg04,
  piu_zzc_machin_b piu_zzc_cfg05, piu_zzc_machin_b piu_zzc_cfg06,
  piu_zzc_machin_b piu_zzc_cfg07, piu_zzc_machin_b piu_zzc_cfg08,
  piu_zzc_machin_b piu_zzc_cfg09, piu_zzc_machin_b piu_zzc_cfg10,
  piu_zzc_machin_b piu_zzc_cfg11, piu_zzc_machin_b piu_zzc_cfg12,
  piu_zzc_machin_b piu_zzc_cfg13, piu_zzc_machin_b piu_zzc_cfg14,
  piu_zzc_machin_b piu_zzc_cfg15, piu_zzc_machin_b piu_zzc_cfg16).
Eval vm_compute in (piu_zzc_prim_b piu_zzc_cfg01, piu_zzc_prim_b piu_zzc_cfg02,
  piu_zzc_prim_b piu_zzc_cfg03, piu_zzc_prim_b piu_zzc_cfg04,
  piu_zzc_prim_b piu_zzc_cfg05, piu_zzc_prim_b piu_zzc_cfg06,
  piu_zzc_prim_b piu_zzc_cfg07, piu_zzc_prim_b piu_zzc_cfg08,
  piu_zzc_prim_b piu_zzc_cfg09, piu_zzc_prim_b piu_zzc_cfg10,
  piu_zzc_prim_b piu_zzc_cfg11, piu_zzc_prim_b piu_zzc_cfg12,
  piu_zzc_prim_b piu_zzc_cfg13, piu_zzc_prim_b piu_zzc_cfg14,
  piu_zzc_prim_b piu_zzc_cfg15, piu_zzc_prim_b piu_zzc_cfg16).
