(* piu_zz_tau_hb_wave3c.v — KB11 Hb 升格候选子片 3/8（1024 段 Hb0-Hb15·机械升格件·零漂移回读断言已过）。
   [KB12 adaptive resplit] 本件=wave3（1024_0..15 重条区）四等分 c/4；引理自 wave3 逐字搬移，语句/体零改写。
   使命：consumer 片 assert (HbN : <封闭语句>) + brace 块逐块升格为独立引理（语句/证明体逐字保留，
         抽取器对每生成件回读 diff 断言通过），使 128 小件可全并行独立编译（各自独立进程内存清零），
         替代 20h 单体磨；本件为候选稿，落地须过试炮与终门，不替代正本。
   依赖：piu_zz_tau_enclosure_bank4（Require Export 链末前件，传递覆盖 bank1..bank3 与 base）、
         piu_zz_poincare_engine、piu_zz_padic_clearing、Stdlib QArith/ZArith/Arith/PArith/Lia/List。
   对标：piu_zz_tau_enclosure.v（3275 行 post-fix·原巨件 md5 494c8738 分段账）zzPhi_512 段 L103-L774 /
         zzPhi_1024 段 L1019-L3034 的 assert (HbN) 块逐字升格。
   构造性：本片语句零假设、零公理；语句全封闭（右边=bank 事实闭式积），
         证明体只吃 bank 引理＋cbn＋reflexivity；块间零依赖边（ledger 实测）。
   编译配方: coqc -time -native-compiler no -q -Q . "" piu_zz_tau_hb_wave3.v *)
Require Export piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
(* src piu_zz_tau_enclosure.v L1187-L1207 (assert Hb8) *)
Lemma piu_zz_hb_1024_8 : piu_zz_zprod_seg 1024%nat (512%nat + 1392%nat) 16%nat = ((if zz_in_Pn 1024 1905%nat then Z.of_nat 1905%nat else 1%Z) * ((if zz_in_Pn 1024 1906%nat then Z.of_nat 1906%nat else 1%Z) * ((if zz_in_Pn 1024 1907%nat then Z.of_nat 1907%nat else 1%Z) * ((if zz_in_Pn 1024 1908%nat then Z.of_nat 1908%nat else 1%Z) * ((if zz_in_Pn 1024 1909%nat then Z.of_nat 1909%nat else 1%Z) * ((if zz_in_Pn 1024 1910%nat then Z.of_nat 1910%nat else 1%Z) * ((if zz_in_Pn 1024 1911%nat then Z.of_nat 1911%nat else 1%Z) * ((if zz_in_Pn 1024 1912%nat then Z.of_nat 1912%nat else 1%Z) * ((if zz_in_Pn 1024 1913%nat then Z.of_nat 1913%nat else 1%Z) * ((if zz_in_Pn 1024 1914%nat then Z.of_nat 1914%nat else 1%Z) * ((if zz_in_Pn 1024 1915%nat then Z.of_nat 1915%nat else 1%Z) * ((if zz_in_Pn 1024 1916%nat then Z.of_nat 1916%nat else 1%Z) * ((if zz_in_Pn 1024 1917%nat then Z.of_nat 1917%nat else 1%Z) * ((if zz_in_Pn 1024 1918%nat then Z.of_nat 1918%nat else 1%Z) * ((if zz_in_Pn 1024 1919%nat then Z.of_nat 1919%nat else 1%Z) * (if zz_in_Pn 1024 1920%nat then Z.of_nat 1920%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1920.
    rewrite piu_zz_inPn_1024_1919.
    rewrite piu_zz_inPn_1024_1918.
    rewrite piu_zz_inPn_1024_1917.
    rewrite piu_zz_inPn_1024_1916.
    rewrite piu_zz_inPn_1024_1915.
    rewrite piu_zz_inPn_1024_1914.
    rewrite piu_zz_inPn_1024_1913.
    rewrite piu_zz_inPn_1024_1912.
    rewrite piu_zz_inPn_1024_1911.
    rewrite piu_zz_inPn_1024_1910.
    rewrite piu_zz_inPn_1024_1909.
    rewrite piu_zz_inPn_1024_1908.
    rewrite piu_zz_inPn_1024_1907.
    rewrite piu_zz_inPn_1024_1906.
    rewrite piu_zz_inPn_1024_1905.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1208-L1228 (assert Hb9) *)
Lemma piu_zz_hb_1024_9 : piu_zz_zprod_seg 1024%nat (512%nat + 1376%nat) 16%nat = ((if zz_in_Pn 1024 1889%nat then Z.of_nat 1889%nat else 1%Z) * ((if zz_in_Pn 1024 1890%nat then Z.of_nat 1890%nat else 1%Z) * ((if zz_in_Pn 1024 1891%nat then Z.of_nat 1891%nat else 1%Z) * ((if zz_in_Pn 1024 1892%nat then Z.of_nat 1892%nat else 1%Z) * ((if zz_in_Pn 1024 1893%nat then Z.of_nat 1893%nat else 1%Z) * ((if zz_in_Pn 1024 1894%nat then Z.of_nat 1894%nat else 1%Z) * ((if zz_in_Pn 1024 1895%nat then Z.of_nat 1895%nat else 1%Z) * ((if zz_in_Pn 1024 1896%nat then Z.of_nat 1896%nat else 1%Z) * ((if zz_in_Pn 1024 1897%nat then Z.of_nat 1897%nat else 1%Z) * ((if zz_in_Pn 1024 1898%nat then Z.of_nat 1898%nat else 1%Z) * ((if zz_in_Pn 1024 1899%nat then Z.of_nat 1899%nat else 1%Z) * ((if zz_in_Pn 1024 1900%nat then Z.of_nat 1900%nat else 1%Z) * ((if zz_in_Pn 1024 1901%nat then Z.of_nat 1901%nat else 1%Z) * ((if zz_in_Pn 1024 1902%nat then Z.of_nat 1902%nat else 1%Z) * ((if zz_in_Pn 1024 1903%nat then Z.of_nat 1903%nat else 1%Z) * (if zz_in_Pn 1024 1904%nat then Z.of_nat 1904%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1904.
    rewrite piu_zz_inPn_1024_1903.
    rewrite piu_zz_inPn_1024_1902.
    rewrite piu_zz_inPn_1024_1901.
    rewrite piu_zz_inPn_1024_1900.
    rewrite piu_zz_inPn_1024_1899.
    rewrite piu_zz_inPn_1024_1898.
    rewrite piu_zz_inPn_1024_1897.
    rewrite piu_zz_inPn_1024_1896.
    rewrite piu_zz_inPn_1024_1895.
    rewrite piu_zz_inPn_1024_1894.
    rewrite piu_zz_inPn_1024_1893.
    rewrite piu_zz_inPn_1024_1892.
    rewrite piu_zz_inPn_1024_1891.
    rewrite piu_zz_inPn_1024_1890.
    rewrite piu_zz_inPn_1024_1889.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1229-L1249 (assert Hb10) *)
Lemma piu_zz_hb_1024_10 : piu_zz_zprod_seg 1024%nat (512%nat + 1360%nat) 16%nat = ((if zz_in_Pn 1024 1873%nat then Z.of_nat 1873%nat else 1%Z) * ((if zz_in_Pn 1024 1874%nat then Z.of_nat 1874%nat else 1%Z) * ((if zz_in_Pn 1024 1875%nat then Z.of_nat 1875%nat else 1%Z) * ((if zz_in_Pn 1024 1876%nat then Z.of_nat 1876%nat else 1%Z) * ((if zz_in_Pn 1024 1877%nat then Z.of_nat 1877%nat else 1%Z) * ((if zz_in_Pn 1024 1878%nat then Z.of_nat 1878%nat else 1%Z) * ((if zz_in_Pn 1024 1879%nat then Z.of_nat 1879%nat else 1%Z) * ((if zz_in_Pn 1024 1880%nat then Z.of_nat 1880%nat else 1%Z) * ((if zz_in_Pn 1024 1881%nat then Z.of_nat 1881%nat else 1%Z) * ((if zz_in_Pn 1024 1882%nat then Z.of_nat 1882%nat else 1%Z) * ((if zz_in_Pn 1024 1883%nat then Z.of_nat 1883%nat else 1%Z) * ((if zz_in_Pn 1024 1884%nat then Z.of_nat 1884%nat else 1%Z) * ((if zz_in_Pn 1024 1885%nat then Z.of_nat 1885%nat else 1%Z) * ((if zz_in_Pn 1024 1886%nat then Z.of_nat 1886%nat else 1%Z) * ((if zz_in_Pn 1024 1887%nat then Z.of_nat 1887%nat else 1%Z) * (if zz_in_Pn 1024 1888%nat then Z.of_nat 1888%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1888.
    rewrite piu_zz_inPn_1024_1887.
    rewrite piu_zz_inPn_1024_1886.
    rewrite piu_zz_inPn_1024_1885.
    rewrite piu_zz_inPn_1024_1884.
    rewrite piu_zz_inPn_1024_1883.
    rewrite piu_zz_inPn_1024_1882.
    rewrite piu_zz_inPn_1024_1881.
    rewrite piu_zz_inPn_1024_1880.
    rewrite piu_zz_inPn_1024_1879.
    rewrite piu_zz_inPn_1024_1878.
    rewrite piu_zz_inPn_1024_1877.
    rewrite piu_zz_inPn_1024_1876.
    rewrite piu_zz_inPn_1024_1875.
    rewrite piu_zz_inPn_1024_1874.
    rewrite piu_zz_inPn_1024_1873.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1250-L1270 (assert Hb11) *)
Lemma piu_zz_hb_1024_11 : piu_zz_zprod_seg 1024%nat (512%nat + 1344%nat) 16%nat = ((if zz_in_Pn 1024 1857%nat then Z.of_nat 1857%nat else 1%Z) * ((if zz_in_Pn 1024 1858%nat then Z.of_nat 1858%nat else 1%Z) * ((if zz_in_Pn 1024 1859%nat then Z.of_nat 1859%nat else 1%Z) * ((if zz_in_Pn 1024 1860%nat then Z.of_nat 1860%nat else 1%Z) * ((if zz_in_Pn 1024 1861%nat then Z.of_nat 1861%nat else 1%Z) * ((if zz_in_Pn 1024 1862%nat then Z.of_nat 1862%nat else 1%Z) * ((if zz_in_Pn 1024 1863%nat then Z.of_nat 1863%nat else 1%Z) * ((if zz_in_Pn 1024 1864%nat then Z.of_nat 1864%nat else 1%Z) * ((if zz_in_Pn 1024 1865%nat then Z.of_nat 1865%nat else 1%Z) * ((if zz_in_Pn 1024 1866%nat then Z.of_nat 1866%nat else 1%Z) * ((if zz_in_Pn 1024 1867%nat then Z.of_nat 1867%nat else 1%Z) * ((if zz_in_Pn 1024 1868%nat then Z.of_nat 1868%nat else 1%Z) * ((if zz_in_Pn 1024 1869%nat then Z.of_nat 1869%nat else 1%Z) * ((if zz_in_Pn 1024 1870%nat then Z.of_nat 1870%nat else 1%Z) * ((if zz_in_Pn 1024 1871%nat then Z.of_nat 1871%nat else 1%Z) * (if zz_in_Pn 1024 1872%nat then Z.of_nat 1872%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1872.
    rewrite piu_zz_inPn_1024_1871.
    rewrite piu_zz_inPn_1024_1870.
    rewrite piu_zz_inPn_1024_1869.
    rewrite piu_zz_inPn_1024_1868.
    rewrite piu_zz_inPn_1024_1867.
    rewrite piu_zz_inPn_1024_1866.
    rewrite piu_zz_inPn_1024_1865.
    rewrite piu_zz_inPn_1024_1864.
    rewrite piu_zz_inPn_1024_1863.
    rewrite piu_zz_inPn_1024_1862.
    rewrite piu_zz_inPn_1024_1861.
    rewrite piu_zz_inPn_1024_1860.
    rewrite piu_zz_inPn_1024_1859.
    rewrite piu_zz_inPn_1024_1858.
    rewrite piu_zz_inPn_1024_1857.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.
