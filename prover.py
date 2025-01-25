#! /usr/bin/env python

from pyparsing import Word, infixNotation, alphas, alphanums, opAssoc
from itertools import product
import os, sys
import argparse


class Formula:
    variable = Word(alphas, alphanums)
    one = Word("1")
    expr = infixNotation(
        variable | one,
        [("-o", 2, opAssoc.RIGHT),
         ("*", 2, opAssoc.RIGHT)])

    next_term = 1

    @classmethod
    def reset_term_index(cls):
        Formula.next_term = 1

    @classmethod
    def get_next_term(cls):
        term = "X_{" + str(Formula.next_term) + "}"
        Formula.next_term += 1
        return term

    @staticmethod
    def new(literal):
        formula = ""
        if ":" in literal:
            term, formula = literal.split(":")
            term = term.strip()
            formula = formula.strip()
        else:
            term = Formula.get_next_term()
            formula = literal
        # cast the argument as a list if it is a string
        if type(formula) == str:
            formula = Formula.expr.parseString(formula, parseAll=True).asList()[0]
        # If it is an atom or the constant 1, the parse result will be a string again
        if formula == "1":
            return One()
        elif type(formula) == str:
            return Atom(formula, term=term)
        elif len(formula) == 3:
            if formula[1].strip() == "-o":
                return Implication(formula[0], formula[2], term=term)
            elif formula[1].strip() == "*":
                return Tensor(formula[0], formula[2], term=term)
        else:
            raise Exception(f"Cannot parse {formula}")

    def __eq__(self, other):
        if not isinstance(other, Formula):
            return False
        elif self.to_s == other.to_s:
            return True
        else:
            return False


class One(Formula):
    def __init__(self):
        self.to_s = "1"
        self.term = "\\star"

    def to_latex(self):
        return "1"

    def polarity(self):
        return []

class Atom(Formula):
    def __init__(self, string, term = None):
        self.to_s = string
        self.term = term

    def to_latex(self):
        return self.to_s

    def polarity(self):
        return [(self.to_s, 1)]

class Tensor(Formula):
    def __init__(self, first, second, term = None):
        self.first  = Formula.new(first)
        self.second = Formula.new(second)
        self.to_s = f"({self.first.to_s} * {self.second.to_s})"
        self.term = term

    def to_latex(self):
        return "(" + self.first.to_latex() + " \\otimes " + self.second.to_latex() + ")"

    def polarity(self):
        return self.first.polarity() + self.second.polarity()

class Implication(Formula):
    def __init__(self, antecedent, consequent, term = None):
        self.antecedent = Formula.new(antecedent)
        self.consequent = Formula.new(consequent)
        self.to_s = f"({self.antecedent.to_s} -o {self.consequent.to_s})"
        self.term = term

    def to_latex(self):
        return "(" + self.antecedent.to_latex() + " \\multimap " + self.consequent.to_latex() + ")"

    def polarity(self):
        return [(s, -p) for (s, p) in self.antecedent.polarity()] + self.consequent.polarity()

class Sequent:
    def __init__(self, left, right):
        for f in left:
            assert isinstance(f, Formula)
        assert isinstance(right, Formula)

        self.left = left
        self.right = right
        self.to_s = f"{', '.join(f"{l.term + ":" if l.term else ""}{l.to_s}" for l in left)} |- {right.to_s}"

    def from_strings(formulae):
        return Sequent([Formula.new(f) for f in formulae[0:-1]], Formula.new(formulae[-1]))

    def to_latex(self):
        return ",".join(l.to_latex() for l in self.left) + " \\vdash " + self.right.to_latex()

    def polarity(self):
        atomic_polarities = sum([f.polarity() for f in self.left], []) + [(s, -p) for (s, p) in self.right.polarity()]
        total_polarities = {}
        for (s, p) in atomic_polarities:
            if s in total_polarities:
                total_polarities[s] += p
            else:
                total_polarities[s] = p
        return total_polarities

    # Return +true+ if there are equal numbers of positive and
    # negative occurrences for all atomic formulae in the
    # sequent. Only such sequents can ever be proven. This is used for
    # pruning when splitting assumptions in the left implication and
    # right tensor rules.  NB: if we ever extend to additive
    # connectives, this must be changed as the heuristic only holds
    # for sequents with only multiplicative connectives
    def balanced(self):
        return all(v == 0 for v in self.polarity().values())

    def is_axiom(self):
        return len(self.left) == 1 and self.left[0] == self.right

    def is_right_one(self):
        return self.left == [] and isinstance(self.right, One)

    # return a proof tree reducing the formula on the right
    def right_reduce(self, prune=True):
        # G, A |- B
        # ---------
        # G |- A -o B
        if isinstance(self.right, Implication):
            return [["RightImp", Sequent(self.left + [self.right.antecedent], self.right.consequent)]]

        # G |- A   D |- B
        # ---------------
        # G, D |- A x B
        elif isinstance(self.right, Tensor):
            A = self.right.first
            B = self.right.second
            if prune:
                return filter(lambda x: x[1].balanced(), [["RightTensor", Sequent(gamma, A), Sequent(delta, B)] for (gamma, delta) in Sequent.split_list(self.left)])
            else:
                return [["RightTensor", Sequent(gamma, A), Sequent(delta, B)] for (gamma, delta) in Sequent.split_list(self.left)]

    def left_reduce(self, i, prune=True):
        # G |- A     D, B |- C
        # --------------------
        #  G, A -o B, D |- C
        if isinstance(self.left[i], Implication):
            A = self.left[i].antecedent
            B = self.left[i].consequent
            new_left = self.left[0:i] + self.left[i+1:]
            if prune:
                return filter(lambda x: x[1].balanced(), [["LeftImp", Sequent(gamma, A), Sequent(delta + [B], self.right)] for (gamma, delta) in Sequent.split_list(new_left)])
            else:
                return [["LeftImp", Sequent(gamma, A), Sequent(delta + [B], self.right)] for (gamma, delta) in Sequent.split_list(new_left)]

        # G, A, B  |- C
        # ---------------
        # G, A x B |- C
        elif isinstance(self.left[i], Tensor):
            A = self.left[i].first
            B = self.left[i].second
            G = self.left[0:i] + self.left[i+1:]
            return [["LeftTensor", Sequent(G + [A, B], self.right)]]

        # G |- C
        # G, 1 |- C
        elif isinstance(self.left[i], One):
            G = self.left[0:i] + self.left[i+1:]
            return [["LeftOne", Sequent(G, self.right)]]

    # cache holding proofs of sequents
    cache = dict()

    # iterate over all complex formulae in the sequent and start
    # proofs from them.
    def prove(self, prune=True):
        # look up if we already did this
        if self.to_s in Sequent.cache:
            return Sequent.cache[self.to_s]

        proofs = []
        # stop recursion if we are at an axiom or a |- 1 sequent
        if self.is_axiom():
            result = [SequentTree(self, "Axiom", [])]
            Sequent.cache[self.to_s] = result
            return result
        elif self.is_right_one():
            result = [SequentTree(self, "RightOne", [])]
            Sequent.cache[self.to_s] = result
            return result
        # else, reduce at all possible points left and right
        for i, l in enumerate(self.left):
            if not isinstance(l, Atom):
                proofs += self.left_reduce(i, prune)
        if not isinstance(self.right, Atom) and not isinstance(self.right, One):
            proofs += self.right_reduce(prune)
        # if no reduction is possible, we have a failed proof, so
        # nothing gets added to the proof list
        # Now, recurse on the non-terminated trees we have
        proof_trees = []
        for proof in proofs:
            proof_trees += [SequentTree(self, proof[0], list(children)) for children in product(*[c.prove(prune) for c in proof[1:]])]
        Sequent.cache[self.to_s] = proof_trees
        return proof_trees


    # returns all possible ways of splitting the list of hypotheses in two
    @staticmethod
    def split_list(liste):
        l1 = []
        l2 = []
        for pattern in product([True, False], repeat = len(liste)):
            l1.append([x[1] for x in zip(pattern, liste) if x[0]])
            l2.append([x[1] for x in zip(pattern, liste) if not x[0]])
        return list(zip(l1, l2))


class ProofTree:
    def label_to_latex(self):
        if self.rule == "Axiom" or self.rule == "Id":
            return "$Id$"
        elif self.rule == "LeftImp":
            return "$\\multimap L$"
        elif self.rule == "RightImp":
            return "$\\multimap R$"
        elif self.rule == "LeftTensor":
            return "$\\otimes L$"
        elif self.rule == "RightTensor":
            return "$\\otimes R$"
        elif self.rule == "LeftOne":
            return "$1 L$"
        elif self.rule == "RightOne":
            return "$1 R$"
        elif self.rule.startswith("ImpIntro-"):
            idx = self.rule.split("-")[1]
            return "$\\rightarrow I_{" + idx + "}$"
        elif self.rule == "ImpElim":
            return "$\\rightarrow E$"
        elif self.rule == "TensorIntro":
            return "$\\otimes I$"
        elif self.rule.startswith("TensorElim-"):
            idx1, idx2 = self.rule.split("-")[-2:]
            return "$\\otimes E_{" + f"{idx1},{idx2}" + "}$"
        elif self.rule == "OneElim":
            return "$1 E$"
        elif self.rule == "OneIntro":
            return "$1 I$"
        elif self.rule == "":
            return ""
        else:
            raise Exception(f"Unknown rule {self.rule}")

    def latex_tree(self):
        return "\\begin{scprooftree}\n" + self.to_latex() + "\\end{scprooftree}"

    def to_latex(self):
        if len(self.children) == 0:
            if isinstance(self, NDTree):
                child_latex = ""
            elif isinstance(self, SequentTree):
                child_latex = "\\AxiomC{}\n"
        else:
            child_latex = "\n".join(c.to_latex() for c in self.children) + "\n"

        if len(self.children) == 2:
            inf_rule = "\\BinaryInfC"
        elif len(self.children) == 1:
            inf_rule = "\\UnaryInfC"
        else:
            if isinstance(self, NDTree):
                inf_rule = "\\AxiomC"
            elif isinstance(self, SequentTree):
                inf_rule = "\\UnaryInfC"
        # replace star with \star (a little hack to avoid accidental capture in the replacement done by TensorElim)
        term = self.term.replace("}star", "}\\star")
        if term != "":
            term = term + " : "
        formula = term + self.node.to_latex()
        if isinstance(self, NDTree) and self.hypothesis:
            formula = "[" + formula + "]_{" + str(self.hypothesis) + "}"
        return child_latex + "\n" + "\\RightLabel{\\tiny " + self.label_to_latex() + "}\n" + inf_rule + "{$" + formula + "$}"


class NDTree(ProofTree):

    def __init__(self, formula, rule, children, hypothesis=None):
        assert isinstance(formula, Formula)
        assert isinstance(children, list)
        for c in children:
            assert isinstance(c, NDTree)
        self.node = formula
        self.rule = rule
        self.children = children
        self.hypothesis = hypothesis
        self.term = None

    next_hypothesis_index = 1

    @classmethod
    def get_next_index(cls):
        i = NDTree.next_hypothesis_index
        NDTree.next_hypothesis_index += 1
        return i

    def leaf_nodes(self):
        if self.children == []:
            return [self]
        else:
            return [l for ls in self.children for l in ls.leaf_nodes()]

    def find_formula_on_leaf_node(self, formula, only_nonhypotheticals=False):
        return [l for l in self.leaf_nodes() if l.node == formula and (l.hypothesis is None or not only_nonhypotheticals)][0]

    def append_children(self, children, new_rule=None):
        assert self.children == []
        self.children = children
        if new_rule:
            self.rule = new_rule

    # TODO: normalisation of tensor elim and intro as well
    def is_normal(self):
        # Major premise is the left [0] daughter
        if self.rule == "ImpElim" and self.children[0].rule.startswith("ImpIntro"):
            return False
        elif self.rule.startswith("ImpIntro") and self.children[0].rule.startswith("ImpElim"):
            idx = int(self.rule.split("-")[1])
            if self.children[0].children[1].hypothesis == idx:
                return False
            else:
                return all(c.is_normal() for c in self.children)
        else:
            return all(c.is_normal() for c in self.children)

    def to_latex(self):
        return super().to_latex()

    # ideally, check for alpha equivalence here
    # Also, maybe check that the term is not None?
    def is_identical(self, other_nd_tree, reduce_tensor):
        return self.term == other_nd_tree.term


    @classmethod
    def reduce_proofs(cls, nd_trees, reduce_tensor):
        res = []
        for nd_tree in nd_trees:
            if nd_tree.is_normal() and not any(t.is_identical(nd_tree, reduce_tensor) for t in res):
                res.append(nd_tree)
        return res

    def assign_terms(self, reduce_tensor):
        self.assign_term(reduce_tensor)
        return self

    # This computes term for all *formulae* objects in the tree and stores that as proof tree's term
    def assign_term(self, reduce_tensor):
        if self.children == [] and self.node.term is not None:
            pass
        elif self.children == []:
            raise Exception("Leaf node without term!")
        elif self.rule == "ImpElim":
            # the major premise is the 0'th child
            self.node.term = self.children[0].assign_term(reduce_tensor) + "(" + self.children[1].assign_term(reduce_tensor) + ")"
        elif self.rule.startswith("ImpIntro-"):
            idx = int(self.rule.split("-")[1])
            var = [l for l in self.leaf_nodes() if l.hypothesis == idx][0].assign_term(reduce_tensor)
            self.node.term = f"\\lambda {var}.{self.children[0].assign_term(reduce_tensor)}"
        elif self.rule == "TensorIntro":
            self.node.term = f"\\langle {self.children[0].assign_term(reduce_tensor)}, {self.children[1].assign_term(reduce_tensor)}\\rangle"
        elif self.rule.startswith("TensorElim-"):
            a = self.children[0].assign_term(reduce_tensor)
            idx1, idx2 = [int(x) for x in self.rule.split("-")[-2:]]
            var1 = [l for l in self.leaf_nodes() if l.hypothesis == idx1][0].assign_term(reduce_tensor)
            var2 = [l for l in self.leaf_nodes() if l.hypothesis == idx2][0].assign_term(reduce_tensor)
            if reduce_tensor:
                self.node.term = self.children[1].assign_term(reduce_tensor).replace(var1, ("\\texttt{fst($" + a + "$)}")).replace(var2, ("\\texttt{snd($" + a + "$)}"))
            else:
                self.node.term = "\\texttt{let}\\ " + a + "\\ \\texttt{be}\\ \\langle " + var1 + "," + var2 + "\\rangle\\ \\texttt{in}\\ " +  self.children[1].assign_term(reduce_tensor)
            
        # as a little hack, we use *star* here, and replace it with
        # \\star only at the end, to avoid it being falsely replaced
        # by the TensorElim- term rule if reduction is active
        elif self.rule == "OneElim":
            self.node.term = "\\texttt{let } " + self.children[0].assign_term(reduce_tensor) + "\\ \\texttt{ be }" + "star" + "\\ \\texttt{ in }\\ " + self.children[1].assign_term(reduce_tensor)
        # We do not need a rule for OneIntro, as this will be taken care of by the formula to term map
        else:
            raise Exception("What?")
        self.term = self.node.term
        return self.term

    def label_to_latex(self):
        return super().label_to_latex()


class SequentTree(ProofTree):
    def __init__(self, sequent, rule, children):
        self.node = sequent
        self.rule = rule
        self.children = children
        self.to_s = self.node.to_s + f"\n----{self.rule}----\n" + "\t".join(c.to_s for c in self.children)
        self.term = ""
        
    def label_to_latex(self):
        return super().label_to_latex()

    def to_latex(self):
        return super().to_latex()

    def assign_term(self):
        pass

    # Extracts the active implication. Should only be called on proof
    # tree nodes with the left implication rule.
    def find_implication(self):
        antecedent = self.children[0].node.right.to_s
        consequent = self.children[1].node.left[-1].to_s
        implication = [f for f in self.node.left if f.to_s == f"({antecedent} -o {consequent})"][0]
        return implication

    # Extracts the active tensor. Should only be called on proof tree
    # nodes with the right tensor rule.
    def find_tensor(self):
        left = self.children[0].node.left[-2].to_s
        right = self.children[0].node.left[-1].to_s
        tensor = [f for f in self.node.left if f.to_s == f"({left} * {right})"][0]
        return tensor

    def to_nd(self):
        if self.rule == "Axiom":
            # pick the left side of the sequent, as this has the term
            return NDTree(self.node.left[0], "Id", [])
        if self.rule == "RightOne":
            return NDTree(self.node.right, "OneIntro", [])
        if self.rule == "LeftOne":
            D = self.children[0].to_nd()
            return NDTree(self.node.right, "OneElim", [NDTree(One(), "", []), D])
        if self.rule == "RightImp":
            D = self.children[0].to_nd()
            a_point = D.find_formula_on_leaf_node(self.node.right.antecedent, only_nonhypotheticals=True)
            i = NDTree.get_next_index()
            a_point.hypothesis = i
            return NDTree(self.node.right, f"ImpIntro-{i}", [D])
        if self.rule == "LeftImp":
            implication = self.find_implication()
            D0 = self.children[0].to_nd()
            D1 = self.children[1].to_nd()
            a_point = D1.find_formula_on_leaf_node(implication.consequent)
            a_point.append_children([NDTree(implication, "", []), D0], "ImpElim")
            return D1
        if self.rule == "RightTensor":
            D0 = self.children[0].to_nd()
            D1 = self.children[1].to_nd()
            return(NDTree(self.node.right, "TensorIntro", [D0, D1]))
        if self.rule == "LeftTensor":
            D0 = self.children[0].to_nd()
            tensor = self.find_tensor()
            a_point = D0.find_formula_on_leaf_node(tensor.first, only_nonhypotheticals=True)
            i = NDTree.get_next_index()
            a_point.hypothesis = i
            b_point = D0.find_formula_on_leaf_node(tensor.second, only_nonhypotheticals=True)
            j = NDTree.get_next_index()
            b_point.hypothesis = j
            return(NDTree(self.node.right, f"TensorElim-{i}-{j}", [NDTree(tensor, "", []), D0]))


if __name__ == "__main__":

    parser = argparse.ArgumentParser(
        prog = 'prover.py',
        description = 'A prover with natural deduction proofs for linear logic')

    parser.add_argument('-i', '--infile', nargs='?', type=argparse.FileType('r'), default=sys.stdin)
    parser.add_argument('-o', '--outfile', nargs='?', type=argparse.FileType('w'), default='proof.tex')
    parser.add_argument('-s', '--sequents', action = 'store_true', default = False)
    parser.add_argument('-q', '--only-sequents', action = 'store_true', default = False)
    parser.add_argument('-a', '--all', action = 'store_true', default = False)
    parser.add_argument('-r', '--rescale', default=0.8)
    parser.add_argument('-d', '--dump-cache', action = 'store_true', default = False)
    parser.add_argument('-p', '--polarity', action = 'store_true', default = False)
    parser.add_argument('-n', '--no-prune', action = 'store_true', default = False)
    parser.add_argument('-l', '--latex-off', action = 'store_true', default = False)
    parser.add_argument('-t', '--tensor-reduction', action = 'store_true', default = False)
    
    args = parser.parse_args()



    formulae = args.infile.read().split(",")
    l = [Formula.new(t) for t in formulae[0:-1]]
    r = Formula.new(formulae[-1])
    s = Sequent(l, r)
    print(f"Searching a proof of {s.to_s}...")

    if args.polarity:
        for i, f in enumerate(l):
            print(f"Assumption {i+1}:\t", f.to_s, "\t\t", f.polarity())
        print(f"Goal:\t\t", r.to_s, "\t\t", r.polarity())
        print("Sequent polarities", s.polarity())

    proofs = s.prove(not args.no_prune)
    print("Done", file=sys.stderr)

    if proofs == []:
        print("Not a theorem", file=sys.stderr)
        exit()
    else:
        args.outfile.write("\\documentclass[landscape]{article}\n")
        args.outfile.write("\\def\\proofscalefactor {" + str(args.rescale) + "}\n")
        args.outfile.write("""\\newenvironment{scprooftree}[0]%
                {\\gdef\\scalefactor{\\proofscalefactor}\\begin{center}\\proofSkipAmount \\leavevmode}%
                {\\scalebox{\\scalefactor}{\\DisplayProof}\\proofSkipAmount \\end{center} }""")
        args.outfile.write("\\usepackage{bussproofs,amssymb,graphicx}\n")
        args.outfile.write("\\usepackage[vmargin=1cm,hmargin=1cm]{geometry}")
        args.outfile.write("\\begin{document}\n")

        if args.sequents or args.only_sequents:
            for i, p in enumerate(proofs):
                args.outfile.write(f"\\noindent Sequent calculus proof nr. {i+1}\\\\")
                args.outfile.write(p.latex_tree())
        if args.only_sequents:
            nd_trees = []
        else:
            print("Converting to natural deduction...", file=sys.stderr)
            nd_trees = [p.to_nd().assign_terms(args.tensor_reduction) for p in proofs]
            print("Done", file=sys.stderr)
        if not args.only_sequents and not args.all:
            print("Normalizing...", file=sys.stderr)
            nd_trees = NDTree.reduce_proofs(nd_trees, args.tensor_reduction)
            print("Done", file=sys.stderr)
        for i, nd_tree in enumerate(nd_trees):
            args.outfile.write(f"\n\\noindent {'N' if args.all else 'Normalised n'}atural deduction proof nr {i+1}\\\\\n")
            args.outfile.write(nd_tree.latex_tree())

        args.outfile.write("\\end{document}")
        args.outfile.close()

        if args.dump_cache:
            print(Sequent.cache, file=sys.stderr)

        if not args.latex_off:
            os.system(f"pdflatex {args.outfile.name}")

        print(f"Proof(s) written to {args.outfile.name}", file=sys.stderr)
