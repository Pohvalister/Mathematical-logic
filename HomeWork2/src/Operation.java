import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Class which covers all operations, including constants (as 0-place operation)
 */
class Operation {
    int childVal;
    String definer;
    String coveredString;
    private int hashCovStr = 0;
    List<Operation> ch;
    Set<String> freeVariables;
    Set<String> fixedVariables;

    private void fixVar(String sym) {
        fixedVariables.add(sym);
        if (freeVariables.contains(sym))
            freeVariables.remove(sym);
        if (ch == null)
            return;
        for (Operation tmp : ch) {
            tmp.fixVar(sym);
        }
    }

    //constants, variables
    Operation(String sym) {
        childVal = 0;
        definer = sym;
        ch = null;
        coveredString = sym;
        freeVariables = new HashSet<>();
        freeVariables.add(sym);
        fixedVariables = new HashSet<>();
    }

    //negation, \'
    Operation(String sym, Operation Child) {
        childVal = 1;
        definer = sym;
        ch = new ArrayList<>(childVal);
        ch.add(Child);
        if (sym.equals("\'"))
            coveredString = '(' + Child.toString() + ')' + sym;
        else
            coveredString = sym + '(' + Child.toString() + ')';
        freeVariables = new HashSet<>(Child.freeVariables);
        fixedVariables = new HashSet<>();
    }

    //+ = & |
    Operation(String sym, Operation leftChild, Operation rightChild) {
        childVal = 2;
        definer = sym;
        ch = new ArrayList<>(2);
        ch.add(leftChild);
        ch.add(rightChild);
        fixedVariables = new HashSet<>();
        if (sym.equals("@") || sym.equals(("?"))) {
            coveredString = sym + leftChild.toString() + '(' + rightChild.toString() + ')';
            freeVariables = new HashSet<>(rightChild.freeVariables);
            freeVariables.remove(leftChild.definer);
            fixedVariables.add(leftChild.toString());
            ch.get(1).fixVar(leftChild.toString());
        } else {
            coveredString = '(' + leftChild.toString() + sym + rightChild.toString() + ')';
            freeVariables = new HashSet<>(leftChild.freeVariables);
            freeVariables.addAll(rightChild.freeVariables);
        }

    }

    //predicates and other multiple operations
    Operation(String sym, List<Operation> Children) {
        childVal = Children.size();
        definer = sym;
        ch = new ArrayList<>(Children);
        coveredString = sym + '(';
        for (Operation tmp : Children)
            coveredString += tmp.toString();
        coveredString += ')';
        freeVariables = new HashSet<>();
        for (Operation tmp : Children)
            freeVariables.addAll(tmp.freeVariables);
        fixedVariables = new HashSet<>();
    }
    //boolean ifLogical(){}

    private int getHash() {
        if (hashCovStr == 0)
            hashCovStr = coveredString.hashCode();
        return hashCovStr;
    }

    boolean isEqualTo(Operation other) {
        return (getHash() == other.getHash()) && (coveredString.equals(other.coveredString));
    }

    boolean isEqualTo(String other) {
        return (coveredString.equals(other));
    }


    public String toString() {
        if (ch == null)
            return coveredString;
        return coveredString;
    }

}
