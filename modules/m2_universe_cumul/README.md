# Module M2：`m2_universe_cumul`（代數宇宙層級、無煩累積小性演算與多項式約束求解器）

本模組為獨立基礎模組（零跨模組依賴），涵蓋依賴類型論之 **宇宙（Universe）** 與 **累積宇宙（Cumulative Universe）** 完整數學結構與決策演算法，直接建構於 2025–2026 前沿論文成果之上：
- **Sterbac & Sterling (2026, arXiv:2607.11329v2, POPL '27)**：*Fuss-free cumulative universes: theory and practice*（合成小性判斷 $\Gamma \vdash A\ \text{small}_i$ 與編解碼算子 $\Downarrow_i / \Uparrow_i$）。
- **Sozeau & Bezem (TYPES 2025 / POPL-RocqPL 2026)**：*Algebraic Universes and Variances For All*（完整代數宇宙 $(0, u, +1, \max)$ 多項式決策、變異性半格與私有宇宙消元）。
- **Jiang, Hu & Oliveira (ICFP 2025)**：*Normalization by Evaluation for Non-cumulativity*（非累積唯一宇宙層級與累積子類型雙模切換）。

---

## 一、資料夾內已獲得之公理、定義、命題、引理與定理列表

1. **全域公理 M2.A1（代數宇宙約束與自然數賦值之伽羅瓦對應）**：在差分約束集 $\mathcal{P}(\mathcal{C}\text{onstr})$ 與賦值空間 $\mathcal{P}(\mathbb{N}^{\mathcal{V}})$ 之間，解集映射 $\Phi(\Psi) = \{\nu \in \mathbb{N}^{\mathcal{V}} \mid \nu \models \Psi\}$ 與理論映射 $\mathrm{Th}(M) = \{c \mid \forall \nu \in M, \nu \models c\}$ 構成反調伽羅瓦連接；語意蘊涵 $\Psi \models \ell_1 \le \ell_2$ 等價於對 $\ell_1$ 各原子項與 $\ell_2$ 全體原子項添加反駁差分邊後不可滿足。
2. **局部公理 M2.A2（無煩累積編解碼消元與私有存在宇宙消元）**：
   - `univ-beta` 與 `univ-ext`：$\Uparrow_i(\Downarrow_i A) \mapsto A$ 且同層重編碼 $\Downarrow_i(\Uparrow_i M) \mapsto M$。
   - Fourier-Motzkin 局部消元：對私有宇宙變數 $e$，橋接 $(a + w_1 \le e) \wedge (e + w_2 \le b) \implies (a + w_1 + w_2 \le b)$ 精確保持公開宇宙變數之可滿足性與蘊涵閉包。
3. **定義 M2.D1（正規代數宇宙表達式 `AlgLevel`）**：任一代數宇宙表示為正規形 $\max(\{c_0\} \cup \{u_m + k_m\})$，滿足後繼分配律 $(\max_r a_r) + 1 = \max_r (a_r + 1)$ 與最小上界結合交換冪等半格律。
4. **定理 M2.T1（無煩衍生累積提升函子性定理）**：定義衍生累積提升 $\uparrow_i^j M := \Downarrow_j(\Uparrow_i M)$，則恆等律 $\uparrow_i^i M = M$ 與複合折疊律 $\uparrow_j^k(\uparrow_i^j M) = \uparrow_i^k M$ 無須額外相干強制轉型公理，完全由局部消元正規化自動導出。
5. **定理 M2.T2（Tarjan 強連通分量無正環判準與點態最小自然賦值定理）**：非負差分約束系統於 $\mathbb{N}$ 可滿足若且唯若任一強連通分量（SCC）內部不含嚴格正權重邊（$w > 0$，排除 $\mathcal{U}_i : \mathcal{U}_i$ 型 Girard/Russell 悖論環）；可滿足時縮點有向無環圖（DAG）之最長路徑動態規劃給出全體模型中之唯一點態最小賦值 $\nu_{\min}$。
6. **命題 M2.P1（參數變異性有界半格與複合單調律）**：變異性標記 $\mathsf{Irrelevant} \sqsubset \mathsf{Covariant} \sqsubset \mathsf{Invariant}$ 構成有界上確界半格與結合複合么半群。
7. **定理 M2.T3（宇宙偏序集之 Ramsey-Dilworth 鏈與反鏈分層對偶定理）**：在任意一致宇宙約束圖導出之嚴格偏序 $(V, \prec)$ 上，最大嚴格鏈高度 $h$ 等於最小反鏈分層數（Mirsky 對偶定理），且恆滿足 Erdős-Szekeres / Ramsey 乘積界 $h \cdot w_{\max} \ge |V|$。

---

## 二、資料夾內已實作之演算法列表

| 演算法名稱 | 所在檔案 | 時間複雜度 | 功能與硬體/數據結構優化說明 |
| :--- | :--- | :--- | :--- |
| 正規代數宇宙半格歸約器 (`AlgLevel::normalize`, `succ`, `lub`, `subst_var`) | `alg_level_fussfree.mbt` | $O(k \log k)$（變數項數 $k$） | 自動合併重複宇宙變數偏移並提升常數下界 |
| 無煩累積編解碼正規化與最小小性合成 (`normalize_fuss_type`, `synthesize_least_smallness`) | `alg_level_fussfree.mbt` | $O(\|A\|)$ | 自動收縮任意層數 $\uparrow_j^k \circ \uparrow_i^j$ 提升鏈並驗證 `Prop` 大消元安全性 |
| 64 變數位元矩陣傳遞可達加速器 (`fast_le_vars`, `record_reach64`) | `constraint_solver_ramsey.mbt` | 查詢 $O(1)$ / 增量更新 $O(64)$ | 以 `FixedArray[UInt64]` 單字組位元測試瞬間判定 $u \le v$ |
| Tarjan SCC + 縮點 DAG 最長路最小賦值與 SPFA 通用差分求解器 (`solve_minimal_valuation`) | `constraint_solver_ramsey.mbt` | 非負圖 $O(V + E)$ / 含負權邊 $O(V \cdot E)$ | 線性時間檢測宇宙悖論正環並構造點態最小自然數模型 |
| 伽羅瓦反駁完備蘊涵決策器 (`entails_le`, `check_level_rel`) | `constraint_solver_ramsey.mbt` | 常數短路 $O(1)$ / 完備決策 $O(k \cdot V \cdot E)$ | 支援任意 $\max / +k$ 代數宇宙不等式蘊涵與累積/非累積模式切換 |
| Fourier-Motzkin 私有宇宙變數局部消元器 (`eliminate_private_vars`) | `constraint_solver_ramsey.mbt` | $O(\|E_{\text{priv}}\| \cdot d_{\text{in}} d_{\text{out}})$ | 消除不透明定義內部私有宇宙變數並去重壓縮公開邊集 |
| Ramsey-Dilworth 偏序鏈與反鏈分層器 (`stratify_ramsey_dilworth`) | `constraint_solver_ramsey.mbt` | $O(V^2 + V \cdot \text{entail})$ | 計算最長嚴格宇宙階層鏈、Mirsky 反鏈層分解與 Ramsey 界驗證 |

---

## 三、資料夾視角的依賴關係圖

```text
                  [ 外部上游依賴：無（純獨立基礎模組） ]
                                    │
                                    ▼
             ┌─────────────────────────────────────────────┐
             │          dtt/m2_universe_cumul              │
             │       alg_level_fussfree.mbt                │
             │                 │                           │
             │                 ▼                           │
             │       constraint_solver_ramsey.mbt          │
             └──────────────┬──────────────┬───────────────┘
                            │              │
          ┌─────────────────┘              └─────────────────┐
          ▼                                                  ▼
[ dtt/m5_fibration_kan ]                         [ dtt/m6_chu_galois_bridge ]
          │                                                  │
          └────────────────────────┬─────────────────────────┘
                                   ▼
                        [ dtt/m7_unified_kernel ]
```

---

## 四、資料夾內動線及接入與輸出接口

### 內部資料動線
1. `alg_level_fussfree.mbt` 定義正規化代數宇宙 `AlgLevel`、變異性半格 `Variance`、雙模枚舉 `HierarchyMode` 以及無煩小性語法 `FussType` / `FussCode` 與大消元守衛。
2. `constraint_solver_ramsey.mbt` 接收 `AlgLevel` 與原子差分約束，同步維護 64 位元可達矩陣 `reach64` 與有向加權邊集 `edges`，提供最小賦值計算、完備伽羅瓦反駁蘊涵決策、私有變數投影消元及 Ramsey-Dilworth 分層分析。

### 輸出公共接口（Public API）
- **類型與錯誤**：`AlgLevel`, `HierarchyMode`, `Variance`, `FussType`, `FussCode`, `DiffEdge`, `UniverseGraph`, `PosetStratification`, `UniverseError`。
- **代數與無煩小性函式**：`AlgLevel::zero`, `AlgLevel::concrete`, `AlgLevel::concrete_clamped`, `AlgLevel::var_offset`, `AlgLevel::normalize`, `AlgLevel::succ`, `AlgLevel::lub`, `AlgLevel::eval_with`, `AlgLevel::subst_var`, `Variance::join`, `Variance::compose`, `fuss_derived_lift`, `normalize_fuss_type`, `normalize_fuss_code`, `synthesize_least_smallness`, `check_prop_elimination`。
- **約束圖與偏序分析函式**：`UniverseGraph::new`, `UniverseGraph::fresh_var`, `UniverseGraph::fast_le_vars`, `UniverseGraph::add_var_le`, `UniverseGraph::add_var_eq`, `UniverseGraph::add_const_floor`, `UniverseGraph::add_const_ceiling`, `UniverseGraph::add_alg_le_var`, `UniverseGraph::solve_minimal_valuation`, `UniverseGraph::is_consistent`, `UniverseGraph::entails_le`, `UniverseGraph::check_level_rel`, `UniverseGraph::eliminate_private_vars`, `UniverseGraph::stratify_ramsey_dilworth`。
