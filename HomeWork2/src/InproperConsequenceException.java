/**
 * Created by pohvalister on 07.02.17.
 */
public class InproperConsequenceException extends Exception {
    private String message;
    private Integer number;

    InproperConsequenceException(String m, Integer i) {
        message = m;
        number = i;
    }

    public String getMessage() {
        return "Вывод некорректен начиная с формулы номер " + number + " : " + message;
    }
}
