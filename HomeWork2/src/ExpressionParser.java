import java.util.ArrayList;
import java.util.List;

/**
 * parses stirng, returns Operation token
 * <p>
 * information of parsing part of string goes through levels of parsing, total 6 levels
 * l r - are variables showing borders of string (l includes, r not)
 */
public class ExpressionParser {
    //a lot of levels are same, differencing only with number
    private char[] levels = {'>', '|', '&', '!', '+', '*'};
    private String str;

    Operation parse(String str1) {
        str = str1.replaceAll(" ", "");
        return implicationStage(0, str.length());

    }

    private Operation implicationStage(int l, int r) {//0
        int balance = 0;
        for (int i = l; i < r; i++) {
            if (str.charAt(i) == ')')
                balance--;
            if (str.charAt(i) == '(')
                balance++;
            if (str.charAt(i) == '>' && balance == 0)
                return new Operation("->", commonCompStage(l, i - 1, 1), implicationStage(i + 1, r));
        }
        return commonCompStage(l, r, 1);
    }

    private Operation commonCompStage(int l, int r, int level) {
        if (level == 3)
            return unarStage(l, r);
        if (level == 6)
            return variableStage(l, r);
        int balance = 0;
        for (int i = r - 1; i >= l; i--) {
            if (str.charAt(i) == ')')
                balance--;
            if (str.charAt(i) == '(')
                balance++;
            if (str.charAt(i) == levels[level] && balance == 0)
                return new Operation("" + str.charAt(i), commonCompStage(l, i, level), commonCompStage(i + 1, r, level + 1));
        }
        return commonCompStage(l, r, level + 1);

    }

    private Operation unarStage(int l, int r) {//3
        if (str.charAt(l) == '!')
            return new Operation("!", unarStage(l + 1, r));
        if (str.charAt(l) == '@' || str.charAt(l) == '?') {
            String tmp = "";
            int i = l + 1;
            while (isFromVar(str.charAt(i))) {
                tmp += str.charAt(i);
                i++;
            }
            return new Operation("" + str.charAt(l), new Operation(tmp), unarStage(i, r));//predicate
        }
        if (str.charAt(l) == '(') {
            int balance = 0;
            for (int i = l; i < r - 1; i++) {
                if (str.charAt(i) == '(')
                    balance++;
                if (str.charAt(i) == ')')
                    balance--;
                if ((str.charAt(i) == ')') && balance == 0)
                    return predicateStage(l, r);
            }
            return implicationStage(l + 1, r - 1);
        }

        return predicateStage(l, r);
    }

    private Operation predicateStage(int l, int r) {
        String predS = "";
        int i = l;
        if (isFromPred(str.charAt(i), true)) {
            while (i != r && isFromPred(str.charAt(i), false)) {
                predS += str.charAt(i);
                i++;
            }
            if (i != r && str.charAt(i) == '(') {
                i++;
                r--;
            }
            List<Operation> tmpList = new ArrayList<>();
            int j, balance = 0;
            for (j = i; j != r + 1; j++) {
                if (j == r) {
                    tmpList.add(commonCompStage(i, j, 4));
                    i = j + 1;
                    continue;
                }
                if (str.charAt(j) == ')') balance++;
                if (str.charAt(j) == '(') balance--;
                if (str.charAt(j) == ',' && balance == 0) {
                    tmpList.add(commonCompStage(i, j, 4));
                    i = j + 1;
                }
            }
            return new Operation(predS, tmpList);//predicate P(...)
        } else {
            for (int j = l; j < r; j++)
                if (str.charAt(j) == '=')
                    return new Operation("=", commonCompStage(l, j, 4), commonCompStage(j + 1, r, 4));
        }
        //throw new InproperConsequenceException();
        return null;

    }

    private Operation variableStage(int l, int r) {//6
        if (l == r)
            return new Operation(str.substring(l, r));
        if (str.charAt(r - 1) == '\'')
            return new Operation("\'", variableStage(l, r - 1));
        if (str.charAt(l) == '0')
            return new Operation("0");
        if (str.charAt(l) == '(')
            return commonCompStage(l + 1, r - 1, 4);
        if (str.charAt(r - 1) == ')') {
            String varS = "";
            int i = l;
            while (isFromVar(str.charAt(i))) {
                varS += str.charAt(i);
                i++;
            }
            if (i != r && str.charAt(i) == '(') {
                i++;
                r--;
            }
            List<Operation> tmpList = new ArrayList<>();
            int j, balance = 0;
            for (j = i; j != r + 1; j++) {
                if (j == r) {
                    tmpList.add(commonCompStage(i, j, 4));
                    i = j + 1;
                    continue;
                }
                if (str.charAt(j) == ')') balance++;
                if (str.charAt(j) == '(') balance--;
                if (str.charAt(j) == ',' && balance == 0) {
                    tmpList.add(commonCompStage(i, j, 4));
                    i = j + 1;
                }
                /*tmpList.add(commonCompStage(i, j, 4));
                i = j + 1;*/
            }
            return new Operation(varS, tmpList);// p(...)

        }
        return new Operation(str.substring(l, r));
    }

    private boolean isFromVar(char c) {
        return (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9');
    }

    private boolean isFromPred(char c, boolean first) {
        if (first)
            return (c >= 'A' && c <= 'Z');
        return (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9');
    }

}

//not useful
  /*
    Operation disjunctionStage(int l, int r) {//1
        int balance = 0;
        for (int i = r - 1; i >= l; i--) {
            if (str.charAt(i) == ')')
                balance--;
            if (str.charAt(i) == '(')
                balance++;
            if (str.charAt(i) == '|' && balance == 0)
                return new BinaryOperator("|", disjunctionStage(l, i - 1), conjunctionStage(i + 1, r));
        }
        return conjunctionStage(l, r);
    }
    Operation conjunctionStage(int l, int r) {//2
        int balance = 0;
        for (int i = r - 1; i >= l; i--) {
            if (str.charAt(i) == ')')
                balance--;
            if (str.charAt(i) == '(')
                balance++;
            if (str.charAt(i) == '&' && balance == 0)
                return new BinaryOperator("&", conjunctionStage(l, i - 1), unarStage(i + 1, r));
        }
        return unarStage(l, r);
    }
*/

    /*Operation summStage(int l, int r) {//4
        int balance = 0;
        for (int i = r - 1; i >= l; i--) {
            if (str.charAt(i) == ')')
                balance--;
            if (str.charAt(i) == '(')
                balance++;
            if (str.charAt(i) == '+' && balance == 0)
                return new BinaryOperator("+", summStage(l, i - 1), multipleStage(i + 1, r));
        }
        return multipleStage(l, r);
    }

    Operation multipleStage(int l, int r) {//5
        int balance = 0;
        for (int i = r - 1; i >= l; i--) {
            if (str.charAt(i) == ')')
                balance--;
            if (str.charAt(i) == '(')
                balance++;
            if (str.charAt(i) == '*' && balance == 0)
                return new BinaryOperator("*", summStage(l, i - 1), variableStage(i + 1, r));
        }
        return multipleStage(l, r);
    }*/
