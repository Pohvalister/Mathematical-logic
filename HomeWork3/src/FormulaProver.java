import java.io.*;

public class FormulaProver {

    public static void main(String[] args){
        int a  =new Integer(args[0]);
        int b = new Integer(args[1]);
        try (PrintWriter writer = new PrintWriter("answer.txt")){
            if (a<=b)
                proveLess(a,b,writer);
            else
                proveNotLess(a,b,writer);
        }catch (IOException excep){
            excep.printStackTrace();
        }
    }

    private static void proveLess(int less,int more,PrintWriter writer)throws IOException{
        String Lstr=valToStr(less);
        String Mstr=valToStr(more);
        writer.println("|-?p(" + Lstr + "+p=" + Mstr+ ")");

        fromReaderToWriter("src/proves/headPart.proof",writer,"","","");
        fromReaderToWriter("src/proves/less_1_RaisingOne.proof",writer,Lstr,"","");
        for (int i=0;i<more -less; i++){
             fromReaderToWriter("src/proves/less_2_CycledRaiseBoth.proof",writer,Lstr,valToStr(i),valToStr(less+i));
        }
        fromReaderToWriter("src/proves/less_3_GetAnswer.proof",writer,Lstr,Mstr,valToStr(more-less));
    }

    private static void proveNotLess(int nLess,int nMore,PrintWriter writer)throws IOException{
        String nLstr=valToStr(nLess);
        String nMstr=valToStr(nMore);
        writer.println("|-@p(!(p+" + nLstr + "=" + nMstr + "))");

        fromReaderToWriter("src/proves/headPart.proof",writer,"","","");
        fromReaderToWriter("src/proves/more_1_RaisingDiff.proof",writer,valToStr(nLess-nMore-1),"","");
        for (int i=0;i<nMore; i++){
            fromReaderToWriter("src/proves/more_2_CycledRaiseBoth.proof",writer,valToStr(nLess-nMore-1+i),valToStr(i),"");
        }
        fromReaderToWriter("src/proves/more_3_ConfirmCycle.proof",writer,valToStr(nLess-nMore-1),"","");
        for (int i=0;i<nMore;i++){
            String tmpStr ="(p+" + valToStr(nLess-nMore-1) + ")'";
            String tmpStr2 = "p+" + valToStr(nLess-nMore-1) + "'";
            fromReaderToWriter("src/proves/more_4_CycledRaiseDiff.proof",writer,addSA(tmpStr,i),addSA(tmpStr2,i),"");
        }
        String tmpStr3 = "(p+" + valToStr(nLess-nMore-1) + ")";
        String tmpStr4 = "p+" + nLstr;
        fromReaderToWriter("src/proves/more_5_GetAnswer.proof", writer,addSA(tmpStr3,nMore+1),tmpStr4,nMstr);
    }

    private static String valToStr(int x){
        String answer="0";
        for (int i = 0;i<x;i++)
            answer+='\'';
        return answer;
    }

    private static String addSA(String str,int x){//addSomeApostrophe
        String answer=str;
        for (int i=0;i<x;i++)
            answer+='\'';
        return answer;
    }

    private static void fromReaderToWriter (String from, PrintWriter to, String AChange, String BChange, String CChange)throws IOException{
        String str;
        try (BufferedReader reader = new BufferedReader(new FileReader(from))){
            while ((str=reader.readLine())!=null){
                to.println(str.replace("_A",AChange).replace("_B",BChange).replace("_C",CChange));
            }
        }
    }
}
