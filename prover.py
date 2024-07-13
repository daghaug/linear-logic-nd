from pyparsing import Word, infixNotation, alphas, alphanums, opAssoc
from itertools import product
import os, sys
import argparse
from copy import deepcopy
from collections import defaultdict


class Formula:
    variable = Word(alphas, alphanums)
    one = Word("1")
    expr = infixNotation(
        variable | one,
        [("-o", 2, opAssoc.RIGHT),
         ("*", 2, opAssoc.RIGHT)])

    @staticmethod
    def new(literal, term=None):
        formula = ""
        if ":" in literal:
            term, formula = literal.split(":")
            term = term.strip()
            formula = formula.strip()
        else:
            formula = literal
            # cast the argument as a list if it is a string
        if type(formula) == str:
            formula = Formula.expr.parseString(formula, parseAll=True).asList()[0]
#        print(f"The formula is {formula} and the term is {term}")
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

class Atom(Formula):
    def __init__(self, string, term = None):
        self.to_s = string
        self.term = term

    def to_latex(self):
        return self.to_s

class Tensor(Formula):
    def __init__(self, first, second, term = None):
        self.first  = Formula.new(first)
        self.second = Formula.new(second)
        self.to_s = f"({self.first.to_s} * {self.second.to_s})"
        self.term = term
        
    def to_latex(self):
        return "(" + self.first.to_latex() + " \\otimes " + self.second.to_latex() + ")"

class Implication(Formula):
    def __init__(self, antecedent, consequent, term = None):
        self.antecedent = Formula.new(antecedent)
        self.consequent = Formula.new(consequent)
        self.to_s = f"({self.antecedent.to_s} -o {self.consequent.to_s})"
        self.term = term
        
    def to_latex(self):
        return "(" + self.antecedent.to_latex() + " \\multimap " + self.consequent.to_latex() + ")"

class Sequent:
    def __init__(self, left, right):
        for f in left:
            assert isinstance(f, Formula)
        assert isinstance(right, Formula)

        self.left = left
        self.right = right
        self.to_s = f"{', '.join(l.to_s for l in left)} |- {right.to_s}"

    def from_strings(formulae):
        return Sequent([Formula.new(f) for f in formulae[0:-1]], Formula.new(formulae[-1]))

    def to_latex(self):
        return ",".join(l.to_latex() for l in self.left) + " \\vdash " + self.right.to_latex()

    def is_axiom(self):
        return len(self.left) == 1 and self.left[0] == self.right

    def is_right_one(self):
        return self.left == [] and isinstance(self.right, One)

    def is_dead_end(self):
        not self.is_axiom and all(isinstance(f, Atom) for f in left) and isinstance(right, Atom)

    # return a proof tree reducing the formula on the right
    def right_reduce(self):
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
            return [["RightTensor", Sequent(gamma, A), Sequent(delta, B)] for (gamma, delta) in Sequent.split_list(self.left)]

    def left_reduce(self, i):
        # G |- A     D, B |- C
        # --------------------
        #  G, A -o B, D |- C
        if isinstance(self.left[i], Implication):
            A = self.left[i].antecedent
            B = self.left[i].consequent
            new_left = self.left[0:i] + self.left[i+1:]
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



    # iterate over all complex formulae in the sequent and start
    # proofs from them.
    def prove(self):
        proofs = []
        # stop recursion if we are at an axiom or a |- 1 sequent
        if self.is_axiom():
            return [SequentTree(self, "Axiom", [])]
        elif self.is_right_one():
            return [SequentTree(self, "RightOne", [])]
        # else, reduce at all possible points left and right
        for i, l in enumerate(self.left):
            if not isinstance(l, Atom):
                proofs += self.left_reduce(i)
        if not isinstance(self.right, Atom) and not isinstance(self.right, One):
            proofs += self.right_reduce()
        # if no reduction is possible, we have a failed proof, so
        # nothing gets added to the proof list
        # Now, recurse on the non-terminated trees we have
        proof_trees = []
        for proof in proofs:
            proof_trees += [SequentTree(self, proof[0], list(children)) for children in product(*[c.prove() for c in proof[1:]])]
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
        return "\\begin{scprooftree}{0.8}\n" + self.to_latex() + "\\end{scprooftree}"

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
        # replace star with \star (a little hack to avoid accidental capture in the replacement done by TensorElim
        term = self.term().replace("}star", "}\\star")
        if term != "":
            term = term + " : "
        formula = term + self.node.to_latex()
        if isinstance(self, NDTree) and self.hypothesis:
            formula = "[" + formula + "]_{" + str(self.hypothesis) + "}"
        return child_latex + "\n" + "\\RightLabel{\\tiny " + self.label_to_latex() + "}\n" + inf_rule + "{$" + formula + "$}"



    
# TODO make sure that hypothetical nodes never get a user-assigned
# term But since nodes can be made hypotheses during creation, this
# means we have to create the tree first and *then* assign terms. This
# also has the advantage that we can more easily turn term assignment
# on and off
class NDTree(ProofTree):

    next_hypothesis_index = 1

    @classmethod
    def get_next_index(cls):
        i = NDTree.next_hypothesis_index
        NDTree.next_hypothesis_index += 1
        return i

    def __init__(self, formula, rule, children, hypothesis=None):
        assert isinstance(formula, Formula)
        assert isinstance(children, list)
        for c in children:
            assert isinstance(c, NDTree)
        self.node = formula
        self.rule = rule
        self.children = children
        self.hypothesis = hypothesis


    next_term = 1

    def get_next_term(cls):
        term = "X_{" + str(NDTree.next_term) + "}"
        NDTree.next_term += 1
        return term

    def assign_terms(self):
        NDTree.next_term = 1
        self.term()
        return self
    
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

    def is_identical(self, other_nd_tree):
        return self.term() == other_nd_tree.term()

    
    @classmethod
    def reduce_proofs(cls, nd_trees):
        res = []
        for nd_tree in nd_trees:
            if nd_tree.is_normal() and not any(t.is_identical(nd_tree) for t in res):
                res.append(nd_tree)
        return res

    def term(self):
        #if self.node.term is not None:
        if self.children == [] and self.node.term is not None:
            pass
        elif self.children == []:
            self.node.term = self.get_next_term()
        elif self.rule == "ImpElim":
            # the major premise is the 0'th child
            self.node.term = self.children[0].term() + "(" + self.children[1].term() + ")"
        elif self.rule.startswith("ImpIntro-"):
            idx = int(self.rule.split("-")[1])
            var = [l for l in self.leaf_nodes() if l.hypothesis == idx][0].term()
            self.node.term = f"\\lambda {var}.{self.children[0].term()}"
        elif self.rule == "TensorIntro":
            self.node.term = f"\\langle {self.children[0].term()}, {self.children[1].term()}\\rangle"
        elif self.rule.startswith("TensorElim-"):
            a = self.children[0].term()
            idx1, idx2 = [int(x) for x in self.rule.split("-")[-2:]]
            var1 = [l for l in self.leaf_nodes() if l.hypothesis == idx1][0].term()
            var2 = [l for l in self.leaf_nodes() if l.hypothesis == idx2][0].term()
            self.node.term = self.children[1].term().replace(var1, ("\\texttt{fst($" + a + "$)}")).replace(var2, ("\\texttt{snd($" + a + "$)}"))
        # as a little hack, we use *star* here, and replace it with
        # \\star only at the end, to avoid it being falsely replaced
        # by the TensorElim- term rule
        elif self.rule == "OneElim":
            self.node.term = "\\texttt{let } " + self.children[0].term() + "\\texttt{ be }" + "star" + "\\texttt{ in } " + self.children[1].term()
    #     # We do not need a rule for OneIntro, as this will be taken care of by the formula to term map
        else:
            raise Exception("What?")
        return self.node.term
        
    def label_to_latex(self):
        return super().label_to_latex()


class SequentTree(ProofTree):
    def __init__(self, sequent, rule, children):
        self.node = sequent
        self.rule = rule
        self.children = children
        self.to_s = self.node.to_s + f"\n----{self.rule}----\n" + "\t".join(c.to_s for c in self.children)

    def label_to_latex(self):
        return super().label_to_latex()

    def to_latex(self):
        return super().to_latex()

    # No proof terms for sequents
    def term(self):
        return ""

    # Extracts the active implication. Should only be called on proof
    # tree nodes with the left implication rule.  TODO: for now,
    # convert to strings, since the implication constructor requires
    # strings...
    # TODO: this creates a new implication (and a new tensor), thus potentially loosing the proof term
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
            return deepcopy(D1) #
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
    parser.add_argument('-a', '--all', action = 'store_true', default = False)

    args = parser.parse_args()



    formulae = args.infile.read().split(",")
    l = [Formula.new(t) for t in formulae[0:-1]]
    r = Formula.new(formulae[-1])
    s = Sequent(l, r)
    print(f"Searching a proof of {s.to_s}...")


    proofs = s.prove()
    print("Done", file=sys.stderr)

    if proofs == []:
        print("Not a theorem", file=sys.stderr)
        exit()
    else:
        args.outfile.write("\\documentclass[landscape]{article}\n")
        args.outfile.write("""\\newenvironment{scprooftree}[1]%
                {\\gdef\\scalefactor{#1}\\begin{center}\\proofSkipAmount \\leavevmode}%
                {\\scalebox{\\scalefactor}{\\DisplayProof}\\proofSkipAmount \\end{center} }""")
        args.outfile.write("\\usepackage{bussproofs,amssymb,graphicx}\n")
        args.outfile.write("\\usepackage[vmargin=1cm,hmargin=1cm]{geometry}")
        args.outfile.write("\\begin{document}\n")

        if args.sequents:
            for i, p in enumerate(proofs):
                args.outfile.write(f"\\noindent Sequent calculus proof nr. {i+1}\\\\")
                args.outfile.write(p.latex_tree())
        print("Converting to natural deduction...", file=sys.stderr)
        nd_trees = [p.to_nd().assign_terms() for p in proofs]
        print("Done", file=sys.stderr)
        if not args.all:
            print("Normalizing...", file=sys.stderr)
            nd_trees = NDTree.reduce_proofs(nd_trees)
            print("Done", file=sys.stderr)
        for i, nd_tree in enumerate(nd_trees):
            args.outfile.write(f"\\noindent {'N' if args.all else 'Normalised n'}atural deduction proof nr {i+1}\\\\")
            args.outfile.write(nd_tree.latex_tree())

        args.outfile.write("\\end{document}")
        args.outfile.close()

        os.system(f"pdflatex {args.outfile.name}")
        print(f"Proof(s) written to {args.outfile.name} and compiled with latex", file=sys.stderr)

#"x : A, Q : A -o B, B"
#"x: A, V: A -o B -o C, y: B, "C"
#"x:A, V:A -o B -o C -o D, y:B, z:C, D"
#"V:A -o B -o T, Q1:(A -o T) -o T, Q2:(B -o T) -o T, T"
#"V: (A * B) -o T, x : A, y : B, T"
#"V: A -o B -o T, <x,y> : A * B, T"
#"V: E1 -o E2 -o T, Q1:(E1 -o T) -o T, Q2:(E2 -o (T * l)) -o T, L: E1 -o (E1 * l), T"
