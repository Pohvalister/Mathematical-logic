import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import static java.lang.Math.min;


class AxiomOperationSupport {
    private Map<String, String> match;

    boolean areSameStructured(Operation expr, Operation axiomSh) {
        match = new HashMap<>();
        return checkStruct(expr, axiomSh);
    }

    private boolean checkStruct(Operation expr, Operation axiomSh) {
        //String veryNeedTmp = axiomSh.ch.get(0).definer;
        if ((axiomSh.childVal == 0 && !axiomSh.definer.equals("!")) || (axiomSh.childVal != 0 && axiomSh.ch.get(0).definer.equals(""))) {
            match.putIfAbsent(axiomSh.coveredString, expr.coveredString);
            return match.get(axiomSh.coveredString).equals(expr.coveredString);
        }
        if (expr.definer.equals(axiomSh.definer) && expr.ch.size() == axiomSh.ch.size()) {
            for (int i = 0; i < expr.ch.size(); i++) {
                if (!checkStruct(expr.ch.get(i), axiomSh.ch.get(i)))
                    return false;
            }
            return true;
        }
        return false;
    }

    private Set<String> getFreeVariables(Operation oper) {
        return oper.freeVariables;
    }

    Integer compareQuantorAndNewInFreeCome(Operation quantor, Operation nw) {//-1 not equal; 0 wrong sequence; 1 OK
        targetChange = null;
        if (!(quantor.definer.equals("@") || quantor.definer.equals(("?"))))
            return -1;
        if (!checkAlmEqual(quantor.ch.get(1), nw, quantor.ch.get(0).definer))
            return -1;
        if (targetChange == null)
            return 1;
        if (guide(quantor.ch.get(1), quantor.ch.get(0), getFreeVariables(targetChange)))
            return 1;
        return 0;
    }

    //method searching whether given variables are not fixed in "place" ,placed in "guider"
    private boolean guide(Operation place, Operation guider, Set<String> comparings) {
        if (!getFreeVariables(place).contains(guider.definer))
            return true;
        if (guider.isEqualTo(place)) {
            for (String tmpStr : comparings) {
                if (place.fixedVariables.contains(tmpStr))
                    return false;
            }
            return true;
        }
        if (place.definer.equals("@") && place.definer.equals("?"))
            return guide(place.ch.get(1), guider, comparings);
        boolean tmpBool = true;
        for (Operation oper : place.ch) {
            if (!guide(oper, guider, comparings))
                tmpBool = false;
        }
        return tmpBool;
    }

    //special method for (F(0)&@x(F(x)->F(x')))->F(t) cheking
    Integer compareQuantorAndFreeUnique(Operation expr) {
        Operation theXFormula = expr.ch.get(0).ch.get(1).ch.get(1).ch.get(0);
        Operation theZeroFormula = expr.ch.get(0).ch.get(0);
        Operation theXSFormula = expr.ch.get(0).ch.get(1).ch.get(1).ch.get(1);
        Operation theNewFormula = expr.ch.get(1);
        String targetU = expr.ch.get(0).ch.get(1).ch.get(0).definer;
        targetChange = new Operation("0");
        if (!checkAlmEqual(theXFormula, theZeroFormula, targetU))
            return -1;
        targetChange = new Operation("(" + targetU + "')");
        if (!checkAlmEqual(theXFormula, theXSFormula, targetU))
            return -1;
        targetChange = null;
        if (!checkAlmEqual(theXFormula, theNewFormula, targetU)) {
            return -1;
        }
        /*if (guide (theXFormula,new Operation(targetU),getFreeVariables(targetChange)))
            return 1;*/
        return 0;
    }


    Operation targetChange;

    boolean checkAlmEqual(Operation master, Operation heir, String target) {
        if (master.definer.equals(target)) {
            if (targetChange == null)
                targetChange = heir;
            return targetChange.toString().equals(heir.toString());
        } else {
            if (!master.definer.equals(heir.definer))
                return false;
            for (int i = 0; i < master.childVal; i++) {
                if (!checkAlmEqual(master.ch.get(i), heir.ch.get(i), target))
                    return false;
            }
            return true;
        }
    }

}
//not useful

/*  public Integer checkAlmEqualWithTarget(Operation master, Operation heir,String target){
        targetChange=null;
        if (!checkAlmEqual(master,heir,target))
            return -1;
        if (targetChange==null)
            return 1;
        if (guide (master,targetChange,getFreeVariables(heir)))
            return 1;
        return 0;
    }*/

/*private boolean searchFor (Operation target, Operation here){
        if (target.equals(here))
            return true;
        else{
            for (Operation tmpOp : here.ch){
                if (searchFor(target,tmpOp))
                    return true;
            }
            return false;
        }
    }*/