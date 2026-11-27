"""mathlean —— 数学命题求解 + Lean 4 机器验证的工作流工具。

设计分工：
  * 确定性的部分（脚手架、编译、扫描、审计、台账）是代码，有测试；
  * 需要判断的部分（证明、反例、审计、形式化）是 agent，由 workflow.js 编排。

见 WORKFLOW.md 与 docs/ARCHITECTURE.md。
"""

__version__ = "1.0.0"
