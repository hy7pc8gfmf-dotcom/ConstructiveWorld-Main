# -*- coding: utf-8 -*-
"""机械验证：15 片去头拼接 ≡ 原文逐字节。"""
import io, os

BASE = r"D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo\CW_ConstructiveWorld_219.v"
OUTDIR = r"D:\ComplexAnalysis\ConstructiveWorld-Main\CW219_split"
SHARDS = [
    ("S01_BaseRing", 1, 3071), ("S02_CauchyComplete", 3072, 6982),
    ("S03_QExp", 6983, 13800), ("S04_RealExpLogConv", 13801, 18733),
    ("S05_AlignmentGRPO", 18734, 24767), ("S06_DiffSamplingGibbs", 24768, 32574),
    ("S07_RealSetoidExpLog", 32575, 41232), ("S08_RealMainlineDPO", 41233, 46820),
    ("S09_EntropyReal", 46821, 53931), ("S10_KVQuantTrig", 53932, 66414),
    ("S11_TP3B5", 66415, 79152), ("S12_B5RecycleSF", 79153, 93447),
    ("S13_NLiveAudit", 93448, 97866), ("S14_B5BatchBlock", 97867, 112163),
    ("S15_TailFEPUp", 112164, 114222),
]

def header_lines(name):
    """从分片头部注释解析声明头部行数（第 2 行）。"""
    with io.open(os.path.join(OUTDIR, name + ".v"), "rb") as f:
        head = f.read(2000).decode("utf-8", errors="replace")
    import re
    m = re.search(r"头部 (\d+) 行", head)
    return int(m.group(1)) if m else 0

def main():
    with io.open(BASE, "rb") as f:
        raw = f.read()
    recon = b""
    for idx, (name, a, b) in enumerate(SHARDS):
        with io.open(os.path.join(OUTDIR, name + ".v"), "rb") as f:
            data = f.read()
        n = header_lines(name)
        chunks = data.split(b"\n")
        body = b"\n".join(chunks[n:]) if n else data
        recon += body
        print("%-24s header=%2d  size=%9d  body_lines=%6d (expect %d)"
              % (name, n, len(data), len(chunks) - n, b - a + 1))
    # 末行换行：原文件以 \n 结尾；S15 body 不含该 \n
    if not recon.endswith(b"\n"):
        recon += b"\n"
    ok = recon == raw
    print("BYTE-IDENTICAL:", ok, "(recon=%d bytes, base=%d bytes)" % (len(recon), len(raw)))
    return 0 if ok else 1

if __name__ == "__main__":
    raise SystemExit(main())
