# Module M9：`m9_coalgebra_stream`（共同代數、無窮流、餘模式覆蓋、時鐘守護生產力與雙模擬等價）

本模組為獨立基礎模組（零跨模組依賴），涵蓋附件二之 **共同代數與無窮流（Coalgebras & Infinite Streams）**，整合 Lambek 終共同代數 $\nu X. A \times X$ 展開（Anamorphism）、Rutten 微分流半環（Hadamard 加法與 Cauchy 卷積乘法之 Leibniz 導數律）、Abel-Pientka-Thibodeau 深度餘模式（Copattern）字典樹覆蓋檢驗、Birkedal-Møgelberg `gDTT` 時鐘守護（$\triangleright$ Later 信用點數）生產力檢驗，以及 Hopcroft-Karp 並查集無限視界共同代數雙模擬判定器。

---

## 一、資料夾內已獲得之公理、定義、命題、引理與定理列表

1. **公理 M9.A1（Lambek 終共同代數泛性質與餘模式外延公理）**：對任意狀態共同代數 $(S, \gamma : S \to A \times S)$，存在唯一共同代數同態 `ana_stream(γ) : S -> InfStream[A]` 使 `hd(ana(s)) = (γ(s)).0` 且 `tl(ana(s)) = ana((γ(s)).1)`；流奇偶分裂 `stream_evens_odds` 與交錯 `stream_interleave` 構成雙模擬同構 $\mathsf{InfStream}[A] \simeq \mathsf{InfStream}[A] \times \mathsf{InfStream}[A]$。
2. **定理 M9.T1（Rutten 形式冪級數流微分半環 Leibniz 定理）**：無窮整數流在點態加法 `stream_add_int`、Cauchy 卷積乘法 `stream_cauchy_mul` 與形式導數 `stream_derivative` 下嚴格滿足微分環導子恆等式：
   $$D(f * g) \;=\; (D f) * g \;+\; f * (D g)$$
3. **定理 M9.T2（深度餘模式字典樹精確分割定理）**：餘模式子句集通過 `check_copattern_coverage` 當且僅當其構造之 `CopatTrie` 無空葉（零遺漏觀測路徑）且無重疊前綴（零冗餘子句），保證餘模式定義具備確定性主歸約。
4. **定理 M9.T3（時鐘守護信用點數生產力健全性定理）**：設建構子 `CSCons` 賦予 $+1$ 守護信用、解構子 `CSTail` 消耗 $-1$ 守護信用、`CSZipAdd`/`CSMapSucc` 保持信用不變；若每個自身調用點 `CSSelfRef` 之淨信用 $\ge 1$，則餘遞歸流定義（如 `fib = cons(0, cons(1, zip(fib, tl(fib))))`）在任意有限步內必產出下一個觀測元素。
5. **定理 M9.T4（Hopcroft-Karp 並查集無限視界雙模擬等價定理）**：對有限狀態流自動機 $M_1, M_2$（輸入預檢初始狀態界、表長與**遷移全域性** `tail_next[i] \in [0, N)`，違者 `InvalidAutomatonState`），並查集雙模擬推進（Bisimulation Up-To Equivalence）在至多 $N_1 + N_2 - 1$ 次合併內精確判定全無窮序列雙模擬等價 $\llbracket M_1 \rrbracket \sim \llbracket M_2 \rrbracket$。

---

## 二、資料夾內已實作之演算法列表

| 演算法名稱 | 所在檔案 | 時間複雜度 | 功能與硬體/數據結構優化說明 |
| :--- | :--- | :--- | :--- |
| 終共同代數展開與迭代堆疊安全投影 (`ana_stream`, `stream_take`, `stream_nth`, `stream_evens_odds`, `stream_interleave`) | `coalgebra_copatterns.mbt` | $O(n)$ 迭代常數堆疊空間 | 消除深層遞歸堆疊溢位 |
| 記憶化 Cauchy 卷積與流導數引擎 (`stream_cauchy_mul`, `stream_derivative`) | `coalgebra_copatterns.mbt` | 前 $n$ 項累計 $O(n^2)$ | 以線性前綴陣列快取避免指數重複展開 |
| 餘模式字典樹覆蓋與冗餘檢驗器 (`check_copattern_coverage`) | `guarded_bisimulation.mbt` | $O(\sum \|p_i\|)$ | 一次建樹同步完成完備性與互斥性檢驗 |
| 時鐘守護信用生產力檢驗器 (`verify_guarded_productivity`) | `guarded_bisimulation.mbt` | $O(\|e\|)$ | 精確接受多重守護下之解構餘遞歸並攔截零守護死循環 |
| Hopcroft-Karp 並查集精確雙模擬求解器 (`are_automata_bisimilar`) | `guarded_bisimulation.mbt` | $O((N_1 + N_2)\,\alpha(N_1 + N_2))$ | 路徑壓縮＋按秩合併在近線性時間內判定無窮流等價 |

---

## 三、資料夾視角的依賴關係圖

```text
                  [ 外部上游依賴：無（純獨立基礎模組） ]
                                    │
                                    ▼
             ┌─────────────────────────────────────────────┐
             │           dtt/m9_coalgebra_stream           │
             │        coalgebra_copatterns.mbt             │
             │        guarded_bisimulation.mbt             │
             └──────────────────────┬──────────────────────┘
                                    │
                                    ▼
                     [ dtt/m12_initial_final_duality ]
                                    │
                                    ▼
                    [ dtt/m14_phase2_unified_system ]
```

---

## 四、資料夾內動線及接入與輸出接口

### 內部資料動線
1. `coalgebra_copatterns.mbt` 定義共同代數 `StreamCoalg` 與終流 `InfStream`，提供展開、奇偶同構與微分卷積算子。
2. `guarded_bisimulation.mbt` 驗證餘模式覆蓋與餘遞歸守護生產力，並對有限狀態流共同代數執行並查集無限雙模擬判定。

### 輸出公共接口（Public API）
- **類型與錯誤**：`StreamCoalg`, `InfStream`, `CopatObs`, `CopatTrie`, `CorecStreamExpr`, `FiniteStreamAutomaton`, `CoalgebraError`。
- **核心函式**：`stream_hd`, `stream_tl`, `ana_stream`, `stream_take`, `stream_nth`, `stream_map`, `stream_zip_with`, `stream_evens_odds`, `stream_interleave`, `fibonacci_stream`, `stream_add_int`, `stream_cauchy_mul`, `stream_derivative`, `check_copattern_coverage`, `verify_guarded_productivity`, `automaton_to_stream`, `are_automata_bisimilar`。
