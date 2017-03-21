import java.io.File;
import java.io.IOException;
import java.io.Writer;
import java.util.*;

public class DeductionMaster {
    private static final String selfPFile = "src/newProofConstruct/selfProof.proof";
    private static final String AxiGuesPFile = "src/newProofConstruct/axiomGuessProof.proof";
    private static final String MPPFile = "src/newProofConstruct/MPProof.proof";
    private static final String allQuanPFile = "src/newProofConstruct/newAllProof.proof";
    private static final String someQuanPFIle = "src/newProofConstruct/newExistsProof.proof";

    private boolean needToConstructNewDeduction;

    private Writer newProofwriter;
    private ExpressionParser parser = new ExpressionParser();
    private List<Operation> axiomsStructList;
    private List<Operation> axiomsEqualList;
    private List<Operation> guesses;

    private Comparator<? super Operation> operComparator = (Comparator<Operation>) (operation, t1) -> (operation.toString()).compareTo(t1.toString());
    private Set<Operation> oldProofToConsec = new TreeSet<>(operComparator);

    /**
     * TreeSet contains all proven parts (needed in MP)
     */
    private Set<String> oldProofToMP = new TreeSet<>();
    /**
     * TreeMap to fast find all A, could be in A->B, for our B
     */
    private Map<String, ArrayList<String>> oldProofMPAvailable = new TreeMap<>();

    private int counter = 1;

    private Operation target;

    /**
     * Class to support all checking operations on Operations
     */
    private AxiomOperationSupport axiomOperationSupport = new AxiomOperationSupport();

    /**
     * Constructor to create new deduction
     *
     * @param guessing  list of hypotesis
     * @param lastGuess target for deduction theorem
     * @param writer    where to write answer
     */
    DeductionMaster(List<Operation> guessing, Operation lastGuess, Writer writer, Operation answer) throws Exception {
        needToConstructNewDeduction = true;
        creationStage();
        newProofwriter = writer;
        String guessString = "";
        for (Operation guess : guessing)
            guessString += guess.toString() + ',';
        guessString = guessString.substring(0, Math.max(0, guessString.length() - 1)) + "|- (" + lastGuess.toString() + ")->" + answer.toString() + '\n';
        writer.write(guessString);
        target = lastGuess;
        guesses = guessing;
        guesses.add(lastGuess);
    }

    /**
     * Constructor to check old deduction
     *
     * @param writer place to write
     */
    DeductionMaster(Writer writer, Operation answer) throws InproperConsequenceException, Exception {
        needToConstructNewDeduction = false;
        creationStage();
        newProofwriter = writer;
        writer.write("|-" + answer.toString() + '\n');
    }

    /**
     * main method, gets expression and checks all kinds of how it can be proven
     * it checks axioms, guesses, deduction rules
     *
     * @param expr new expression to prove
     * @throws InproperConsequenceException when nothing is suitable
     */
    void insert(Operation expr) throws InproperConsequenceException, Exception {
        InproperConsequenceException trigger = new InproperConsequenceException("неизвестная ошибка", counter);
        if (needToConstructNewDeduction && expr.isEqualTo(target)) {//same
            proofFromFile(selfPFile, expr.toString(), expr.toString(), target);
            accept(expr);
            return;
        }
        for (Operation axiom : axiomsEqualList)//lastAxioms
            if (expr.isEqualTo(axiom)) {
                proofFromFile(AxiGuesPFile, expr.toString(), expr.toString(), target);
                accept(expr);
                return;
            }
        for (Operation axiom : axiomsStructList)//firstAxioms
            if (axiomOperationSupport.areSameStructured(expr, axiom)) {
                proofFromFile(AxiGuesPFile, expr.toString(), expr.toString(), target);
                accept(expr);
                return;
            }
        if (needToConstructNewDeduction)
            for (Operation axiom : guesses)//guesses
                if (expr.isEqualTo(axiom)) {
                    proofFromFile(AxiGuesPFile, expr.toString(), expr.toString(), target);
                    accept(expr);
                    return;
                }

        if (oldProofMPAvailable.containsKey(expr.toString())) {//MPrule
            for (String check : oldProofMPAvailable.get(expr.toString()))
                if (oldProofToMP.contains(check)) {
                    proofFromFile(MPPFile, check, expr.toString(), target);
                    accept(expr);
                    return;
                }
        }

        if (expr.definer.equals("->")) {//predicateAxioms
            if (expr.ch.get(1).definer.equals("?")) {
                Operation quantor = expr.ch.get(1);
                Operation newFormula = expr.ch.get(0);
                Integer result = axiomOperationSupport.compareQuantorAndNewInFreeCome(quantor, newFormula);
                if (result == 1) {
                    proofFromFile(AxiGuesPFile, expr.toString(), expr.toString(), target);
                    accept(expr);
                    return;
                } else if (result == 0)
                    trigger = new InproperConsequenceException("терм " + axiomOperationSupport.targetChange.toString() + " не свободен для подстановки в формулу вместо переменной " + expr.ch.get(1).ch.get(0).toString(), counter);
            }
            if (expr.ch.get(0).definer.equals("@")) {
                Operation quantor = expr.ch.get(0);
                Operation newFormula = expr.ch.get(1);
                Integer result = axiomOperationSupport.compareQuantorAndNewInFreeCome(quantor, newFormula);
                if (result == 1) {
                    proofFromFile(AxiGuesPFile, expr.toString(), expr.toString(), target);
                    accept(expr);
                    return;
                } else if (result == 0)
                    trigger = new InproperConsequenceException("терм " + axiomOperationSupport.targetChange.toString() + " не свободен для подстановки в формулу вместо переменной" + expr.ch.get(0).ch.get(0).toString(), counter);
            }
        }

        if (expr.ch.get(0).definer.equals("?")) {//predicate Consequence
            for (Operation proof : oldProofToConsec) {
                if (proof.definer.equals("->")) {
                    axiomOperationSupport.targetChange = null;
                    String variable = expr.ch.get(0).ch.get(0).definer;
                    Operation proofQuantorPart = proof.ch.get(0);
                    Operation proofNonQuantorPart = proof.ch.get(1);
                    Operation exprQuantorPart = expr.ch.get(0).ch.get(1);
                    Operation exprNonQuantorPart = expr.ch.get(1);

                    if (axiomOperationSupport.checkAlmEqual(proofQuantorPart, exprQuantorPart, variable) && exprNonQuantorPart.isEqualTo(proofNonQuantorPart)) {
                        if (exprNonQuantorPart.freeVariables.contains(variable)) {
                            trigger = new InproperConsequenceException("переменная " + variable + " входит свободно в формулу " + exprNonQuantorPart.toString(), counter);
                        } else if (needToConstructNewDeduction&&target.freeVariables.contains(variable)) {
                            trigger = new InproperConsequenceException("используется правило с квантором по переменной " + variable + ", входящей свободно в допущение " + target.toString(), counter);
                        } else {
                            if (!needToConstructNewDeduction) {
                                newProofwriter.write(expr.toString() + '\n');
                                return;
                            } else
                                proofFromFile(someQuanPFIle, exprQuantorPart.toString(), exprNonQuantorPart.toString(), expr.ch.get(0).ch.get(0).toString(), target);
                            accept(expr);
                            return;
                        }
                    }
                }
            }
        }
        if (expr.ch.get(1).definer.equals("@")) {//predicate Consequence
            for (Operation proof : oldProofToConsec) {
                if (proof.definer.equals("->")) {
                    axiomOperationSupport.targetChange = null;
                    String variable = expr.ch.get(1).ch.get(0).definer;
                    Operation proofQuantorPart = proof.ch.get(1);
                    Operation proofNonQuantorPart = proof.ch.get(0);
                    Operation exprQuantorPart = expr.ch.get(1).ch.get(1);
                    Operation exprNonQuantorPart = expr.ch.get(0);

                    if (axiomOperationSupport.checkAlmEqual(proofQuantorPart, exprQuantorPart, variable) && exprNonQuantorPart.isEqualTo(proofNonQuantorPart)) {
                        if (exprNonQuantorPart.freeVariables.contains(variable)) {
                            trigger = new InproperConsequenceException("переменная " + variable + " входит свободно в формулу " + exprNonQuantorPart.toString(), counter);
                        } else if (needToConstructNewDeduction&&target.freeVariables.contains(variable)) {
                            trigger = new InproperConsequenceException("используется правило с квантором по переменной " + variable + ", входящей свободно в допущение " + target.toString(), counter);
                        } else {
                            if (!needToConstructNewDeduction) {
                                newProofwriter.write(expr.toString() + '\n');
                                return;
                            } else
                                proofFromFile(allQuanPFile, exprNonQuantorPart.toString(), exprQuantorPart.toString(), expr.ch.get(1).ch.get(0).toString(), target);
                            accept(expr);
                            return;
                        }

                    }
                }
            }
        }
        try {
            Integer tmp = axiomOperationSupport.compareQuantorAndFreeUnique(expr);
            if (tmp != 1) {
                proofFromFile(AxiGuesPFile, expr.toString(), expr.toString(), target);
                accept(expr);
                return;

            }
           /* if (tmp == 0) {
                Operation term = axiomOperationSupport.targetChange;
                Operation formula = expr.ch.get(0).ch.get(1).ch.get(1).ch.get(0);
                Operation variable = expr.ch.get(0).ch.get(1).ch.get(0);
                trigger = new InproperConsequenceException("терм  " + term.toString() + " не свободен для подстановки в формулу " + formula.toString() + " вместо переменной " + variable.toString(), counter);
            }*/
        } catch (Exception e) {
            throw trigger;
        }
        throw trigger;
    }


    /**
     * Method to add expr as proven to needed stuctures
     *
     * @param expr proven expression
     */
    private void accept(Operation expr) {
        counter++;
        if (expr.definer.equals("->"))
            oldProofToConsec.add(expr);
        oldProofToMP.add(expr.toString());
        if (expr.definer.equals("->")) {
            ArrayList<String> tmp;
            if (oldProofMPAvailable.containsKey(expr.ch.get(1).toString()))
                tmp = oldProofMPAvailable.get(expr.ch.get(1).toString());
            else
                tmp = new ArrayList<>();

            tmp.add(expr.ch.get(0).toString());

            oldProofMPAvailable.put(expr.ch.get(1).toString(), tmp);
        }
    }

    /**
     * Method to print new deduction
     *
     * @param fileDir file where to get code
     * @param Aexpr   expr named "_A" in file
     * @param Bexpr   expr named "_B" in file (sometimes not used)
     * @param target  expr named "_T" in file
     */
    private void proofFromFile(String fileDir, String Aexpr, String Bexpr, Operation target) {
        try {
            if (!needToConstructNewDeduction) {
                newProofwriter.write(Bexpr + '\n');
                return;
            }
            Scanner proofIn = new Scanner(new File(fileDir));
            while (proofIn.hasNext()) {
                newProofwriter.write(proofIn.nextLine().replace("_A", Aexpr).replace("_T", target.toString()).replace("_B", Bexpr) + '\n');
            }
            proofIn.close();
        } catch (IOException e) {
            System.out.print("no file");
        }
    }

    private void proofFromFile(String fileDir, String Aexpr, String Bexpr, String dexpr, Operation target) {
        try {
            Scanner proofIn = new Scanner(new File(fileDir));
            while (proofIn.hasNext()) {
                newProofwriter.write(proofIn.nextLine().replace("_A", Aexpr).replace("_T", target.toString()).replace("_B", Bexpr).replace("_d", dexpr) + '\n');
            }
            proofIn.close();
        } catch (IOException e) {
            System.out.print("no file");
        }
    }

    /**
     * before starting proving deduction all axioms needed to be created
     */
    private void creationStage() {
        final String axiomStruct[] = {
                "F()->Q()->F()",
                "(F()->Q())->(F()->Q()->W())->(F()->W())",
                "F()->(Q()->F()&Q())",
                "F()&Q()->F()",
                "F()&Q()->Q()",
                "F()->F()|Q()",
                "F()->Q()|F()",
                "(F()->Q())->(W()->Q())->(F()|W()->Q())",
                "(F()->Q())->(F()->!Q())->!F()",
                "!!F()->F()"
        };
        final String axiomEqual[] = {
                "a=b->a\'=b\'",
                "a=b->a=c->b=c",
                "a\'=b\'->a=b",
                "!(a'=0)",
                "a+b\'=(a+b)\'",
                "a+0=a",
                "a*0=a",
                "a*b'=a*b+a",
        };
        axiomsEqualList = new ArrayList<>();
        axiomsStructList = new ArrayList<>();
        for (String tmpStr : axiomStruct)
            axiomsStructList.add(parser.parse(tmpStr));
        for (String tmpStr : axiomEqual)
            axiomsEqualList.add(parser.parse(tmpStr));
        //comboAxiom = parser.parse("(F()&@f(E()->P()))->G()");

    }
}