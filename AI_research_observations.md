# Observations on AI-assisted long-horizon mathematical research

*Companion note to* `odd_tori_merged_manuscript_v7.tex`.
*Author: SangHyun Park.*
*May 2026.*

This is an informal field note, not a research paper.  It records the
author's observations on two failure modes of GPT-5.5 Pro that surfaced
repeatedly during the multi-month development of the all-odd-modulus
Hamilton-decomposition project for $D_d(m)$.  The companion manuscript
itself relies on the *outputs* of that collaboration; this note records the
*process* failures that the author had to repair by hand.

The two failure modes are independent.  They both pose obstacles to the
goal of AI-driven mathematical research, and they both seem to be invisible
from inside a single short conversation.

## 1. Failure mode A: long-horizon branch-split divergence

The clearest instance arose in the dimension-five Route~E phase.  Route~E
was a candidate proof scheme for $D_5(m)$ that proceeded by splitting the
problem into sub-cases according to the structure of a particular
intermediate object.  Each sub-case looked locally tractable; refining one
of them produced two further sub-cases; refining each of those produced
two more.  The model would attempt one branch, succeed locally,
re-encounter a structurally similar obstacle one level deeper, and split
again, with no sign of recognising that the entire descent was a
non-converging tree.

Several observations stand out.

- **The model did not lack mathematical taste at the local level.**  Each
  individual branch split was a reasonable move.  The failure was not in
  any single step.

- **The failure was at the level of research hypothesis, not tactic.**  A
  human researcher recognises after two or three layers that a particular
  *line of attack* is dead and changes the high-level plan.  The model did
  not perform this re-evaluation.  It treated each new layer as a fresh
  local problem.

- **Asking the model whether the line was productive did not help.**  When
  asked directly, the model would generate a plausible argument that the
  current branch was almost there, or list optimistic sub-conditions it
  thought it could close, and then resume the same recursive split.  Even
  when prompted with explicit "this is not converging" framings, the model
  reverted to local optimisation within a turn or two.

- **The break came from the human author abandoning Route~E entirely.**
  The eventual proof for $D_5$ uses a different mechanism (the first-return
  count, with $m=3$ recorded as a finite certificate).  No salvageable
  fragment of Route~E appears in the final manuscript.

The structural analogue is reinforcement learning that gets trapped in
locally improving but globally unproductive trajectories.  At the research
level, the missing capacity is the ability to ask, of an entire branch of
sub-problems, *"is this tree the right tree?"* and to act on the answer.

The takeaway, as a research methodology question, is that long-horizon
mathematical research with current models cannot be left to run
autonomously over weeks: the branch-split divergence will dominate.  The
author's role in this project was, more often than is comfortable to
admit, to interrupt the model and force a change of plan.

## 2. Failure mode B: known-hard-problem withdrawal

The second failure mode is almost the opposite, and it appeared whenever
the project drifted close to a problem that the model recognised as
classically hard.

The pattern was: the conversation reaches a sub-question (e.g., a Hamilton
decomposition question for an even-modulus torus, or a question about
Cayley digraphs of non-abelian groups, or a question that touches a
classical conjecture).  The model identifies the sub-question as a known
hard or open problem.  At that point it stops trying to construct a proof
or a counterexample and switches to *summarisation mode*: a careful
account of what is known, who proved what, what the current obstacles are,
and a closing note that the question is open.

This is, in itself, useful.  Reliable summarisation of a literature
position is a research service.  The problem is that the model does not
*come back out* of summarisation mode within the same turn.  It does not
attempt a new conjecture, propose a partial result, attempt a falsification
under restricted hypotheses, or test a numerical instance to look for
structure.  It treats "this is known to be hard" as a terminating
condition.

A human researcher's response to "this is hard" is the opposite.  Hard
problems are precisely the ones that warrant further attempts: a partial
result, a relaxed conjecture, an explicit small case, a structural reason
the problem is hard.  The model's withdrawal forecloses all of these.

The clearest instance during the project was the even-modulus case for
$D_d(m)$, recorded in the manuscript only as future work.  The model
recognised this case as known to be substantially different from the odd
case (it is) and from that point would not attempt any structural attack
on it.  Asking it to try a small case (e.g., $D_3(4)$ explicitly) produced
either a refusal in the form of further context, or a generic "this seems
hard" response without an actual attempt.

It is unclear whether this is a training-data artifact (the model has
seen many texts that say "this problem is open" and learned that the
appropriate continuation is information rather than attack), a safety
behaviour (avoid asserting a result on a known-open problem), or
both.  Whatever the cause, the practical effect is that the model has a
reflex to *not try*.

## 3. Why this matters for the next step

The eventual goal of AI mathematical research is for AI to advance from
*assistant* to *researcher*.  The two failure modes above are obstacles
to that transition.

Failure mode A means the model cannot, on its own, run a long enough
research process to find non-trivial results, because it cannot
recognise when a research direction is wrong and needs to be abandoned.
A research project at the scale of the present manuscript could not have
been completed by the model without external direction.

Failure mode B means the model will not, of its own accord, attack the
problems that *most need attacking*.  An autonomous AI researcher that
withdraws from every known hard problem is, by construction, restricted
to easy problems.  But the questions that benefit most from real research
work are the hard ones.

The pair of failures is the more striking part.  Together they create a
basin of acceptable behaviour that is exactly the wrong basin: try
indefinitely on locally improving but unproductive lines, and stop trying
the moment a problem is recognised as genuinely hard.  The human
researcher's instinct is the inversion of this: drop dead branches early,
attack hard problems hard.

## 4. Mitigations used in the present project

These are not solutions; they are workarounds.

- **External hypothesis tracking.**  The author kept written notes,
  outside the model conversation, of which research hypotheses had been
  tried and rejected, in what order, with what evidence.  This document
  was the actual continuity of the project and was the place where dead
  branches were recorded as dead.  The model never had a stable memory of
  which branches had been killed.

- **Explicit "abandon and restart" prompts.**  When a recursive branch
  split was diagnosed, the author would close the conversation, open a
  new one, and start with a problem statement that did not contain the
  abandoned vocabulary.  This worked surprisingly well, and is itself
  evidence that the failure mode is partly conversational momentum.

- **Forcing a small case for known-hard problems.**  Asking the model to
  exhibit a small instance, write a brute-force enumeration, or fit a
  result to data was sometimes enough to break the withdrawal reflex.
  Once the model had produced explicit data, attempts at structural
  conjectures returned.

- **Lean as ground truth.**  The Lean~4 formalisation was the only
  ground-truth check the author did not have to maintain personally.
  When the model produced a candidate proof, the author would attempt to
  formalise it.  Failures of formalisation became failures of the
  candidate proof, and not every candidate survived.  Ground truth
  attached to a checker is, in the author's experience so far, the most
  effective single mitigation against both failure modes.

## 5. What this note is, and is not

This note is a private observation, not a benchmark, not a study, and not
a critique.  It records what the author saw, in one extended project,
with one model, in one period (2026).  Other users with other projects
may see other patterns.  It is recorded here so that the manuscript itself
can stay on its mathematical content, while the messy methodological
observations attached to its production are not lost.
