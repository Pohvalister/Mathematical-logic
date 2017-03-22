import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

public class MAIN {
    private static ExpressionParser expressionParser = new ExpressionParser();
    private static List<Operation> guesses = new ArrayList<>();

    public static void main(String[] args) throws Exception {
        DeductionMaster deductionMaster;
        Operation answer;
        Operation lastGuess;
        if (args.length<2)
            return;
        String fileToInsert=args[1];
        try (FileWriter writer = new FileWriter(fileToInsert)){
            writer.write("");
        }
        catch (Exception e ){
            System.err.println("error with writing occured");
        }
        try (FileWriter fileWriter = new FileWriter(fileToInsert, true)) {

            //System.out.println(Runtime.getRuntime().maxMemory());
            Scanner in = new Scanner(new File(args[0]));
            String tmpStr = in.nextLine();
            if (tmpStr.contains("|-") && !tmpStr.split("\\|-")[0].equals("")) {
                int i1 = 0, balance = 0;
                String expr = "";
                while (!tmpStr.substring(i1, i1 + 2).equals("|-")) {
                    if (tmpStr.charAt(i1) == ',' && balance == 0) {
                        guesses.add(expressionParser.parse(expr));
                        expr = "";
                    } else {
                        if (tmpStr.charAt(i1) == '(')
                            balance++;
                        if (tmpStr.charAt(i1) == ')')
                            balance--;
                        expr += tmpStr.charAt(i1);
                    }
                    i1++;
                }
                lastGuess = (expressionParser.parse(expr));

                answer = expressionParser.parse(tmpStr.split("\\|-")[1]);
                deductionMaster = new DeductionMaster(guesses, lastGuess, fileWriter,answer);
            } else {
                if (tmpStr.contains("|-"))
                    deductionMaster = new DeductionMaster(fileWriter,expressionParser.parse(tmpStr.split("\\|-")[1]));
                else
                    deductionMaster = new DeductionMaster(fileWriter,expressionParser.parse(tmpStr));
            }

            //int VeryNeedCount = 0;
            while (in.hasNext()) {
                deductionMaster.insert(expressionParser.parse(in.nextLine()));
                //VeryNeedCount++;
                //System.out.println("" + VeryNeedCount);
            }
        } catch (IOException e) {
            System.out.println(e.getMessage());
        } catch (InproperConsequenceException e) {
            try (FileWriter newfileWriter = new FileWriter("answer", false)) {
                newfileWriter.write(e.getMessage());
            } catch (IOException ex) {
                System.out.println(ex.getMessage());
            }
        }
    }
}
