# Paper B · Proof graph and evidence legend

**R0003 source cut.** These graphs are intentionally *smaller* than the module import graph. They present logical architecture, not a claim to have machine-extracted every constant in the elaborated proof term. The machine-readable edges, with evidence classification, live in `04_PROOF_EDGE_COURT.csv` and `02_INTEGRATED_ATLAS_DATA.json`.

## Diagram A — Two branches at the final theorem

```mermaid
flowchart TB
 P["Printed public theorem\npaperB_printed_terminal"]
 E["Exact printed difference identity"]
 N["Native PaperBTerminalStatement\nvia Thistle's LOW=0"]
 A["Printed A Euler quotient bridge"]
 B["Printed B squarefree/centered bridge"]
 L["LOW exactly empty\nJlow=0"]
 T["Native terminal consumer\nLOW/CORE/LONG/HIGH"]
 C["CORE: five physical cells"]
 G["LONG: seven physical cells"]
 H["HIGH: bounded Oq(1)"]
 S["Suzuki paid\nVaaler/source adapters"]
 W["WeilHyp from GenKloosterman\nsource-matched bridge"]
 P --> E
 P --> N
 E --> A
 E --> B
 N --> L
 N --> T
 T --> C
 T --> G
 T --> H
 T --> S
 G --> W
 classDef sem fill:#daf7f1,stroke:#217e76,color:#102d2a;
 classDef ana fill:#fff1d2,stroke:#b18132,color:#36250c;
 class P,E,A,B sem;
 class N,L,T,C,G,H,S,W ana;
```

**Interpretation:** arrows are proof-source dependencies or transparent semantic condensations. The top printed theorem has two direct named mathematical inputs. The lower boxes compress intermediate Lean declarations and must not be mistaken for one-step `exact` calls. Use the typed edge CSV for that distinction.

## Diagram B — Physical source conservation

```mermaid
flowchart TD
 F["Original signed physical Central source"]
 LO["LOW: |e| < Jlow"]
 MID["MIDDLE: Jlow ≤ |e| < Jhigh"]
 HI["HIGH: |e| ≥ Jhigh"]
 LONG["LONG: longEither δ"]
 CORE["CORE: not longEither δ"]
 LC["WL | CL | RL | ManyL | EdgeL | ResL | WRL"]
 CC["W | C | R | ResA | Band"]
 Z["Specialization Jlow = 0"]
 F --> LO
 F --> MID
 F --> HI
 MID --> LONG
 MID --> CORE
 LONG --> LC
 CORE --> CC
 Z -. "LOW = 0; no parent omitted" .-> LO
 Z -. "all low parents become MIDDLE" .-> MID
 classDef src fill:#d7eefa,color:#173e50,stroke:#417e9a;
 class F,MID src;
```

The exact three-sector source identity is `Merivelle.Central.regionSum_three_sectors` (`ThreeSectorConsumer.lean:84–92`). The exact complement identity is `Merivelle.Central.foldedMiddle_long_core` (`MiddleLongCoreConsumer.lean:19–26`). The five- and seven-cell identities are `QuillonCoreFinal.pair_decomp` and `QuillonLongFinal.long_pair_decomp`. Their precise masked definitions—not this graphic—are authoritative.

## Diagram C — How quantitative claims propagate

```mermaid
flowchart LR
 A["12 physical cell rates"] --> B["Sum disjoint cells\nCORE ≤ 5Λ^499/500\nLONG ≤ 7Λ^19/20"]
 B --> C["Decoration mass once\nΛ^1/1000"]
 C --> D["CORE ≤ 1280e^10Λ^999/1000\nLONG ≤ 1792e^10Λ^951/1000"]
 D --> E["∀ ε>0 select H0\nSourceUniformSublog"]
 E --> F["LOW/MIDDLE/HIGH\nfolded → active"]
 F --> G["Native theorem"]
 G --> H["Printed theorem via exact Euler identity"]
```

This records the **mathematical mechanism** of rate transport. It does not assert one direct Lean theorem-call edge between each adjacent graphic box. The exact nested epsilon allocation (including the folded-to-active error) is in the main exposition and Pass 5 ledger.

## Evidence legend

| Code | What the record supports | What it does not support |
|---|---|---|
| `direct` | Consumer's visible proof text names the supplier declaration | Full elaborated proof-term transitive closure |
| `via` | Named or mathematically explicit dependency through intervening declarations | That the boxes are adjacent in the kernel DAG |
| `method` | The cell lemma feeds a sector assembly, via named intermediate estimates and triangle bounds | That the sector directly invokes the final cell in one step |
| `source_inspected` | Exact cited archived bytes, their SHA-256, and statement/body location inspected | Fresh local Lean replay or an independent mathematical correctness verdict |
| `external novelty` **unresolved** | Classical names and current-file mechanism classification | Priority/originality relative to all earlier mathematics |

**Important scope:** the RC archive has 675 modules import-reachable from `PaperB.lean`, but this is an import-reachability fact. This atlas does not equate it to the final theorem's transitive proof-constant count. A future elaborator audit would require exact proof-expression extraction, not just source or import inspection.

## Reuse contracts

The unified JSON contains:

- `terminal_nodes`: 16 source-anchored declarations at the endgame.
- `proof_edges`: 26 typed edges, all distinguished by `direct`, `via`, or `method` standing.
- `cards`: 62 mathematical mechanisms (15 Euler/finite, 35 analytic engines, 12 physical cells).
- `cells`: twelve full six-step physical traces, exact masks, methods, rate ladders, limits and original-code excerpts.
- `power_graph`: Pass 5's separately typed 41-node/41-edge quantitative propagation graph.
- `equation_transitions`: 25 A/B/finite-dictionary steps.
- `parameters`: 21 symbol and quantifier records.
- `sources`: 70 distinct SHA-256-identified source files.

A reader may reuse those machine-readable objects to prepare mathematical expositions or independent source reviews. A citation to this atlas is not a substitute for citing the original file and declaration stored on that object.
