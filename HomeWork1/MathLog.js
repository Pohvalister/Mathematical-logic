var VAL = function (smth) {
    this.assosiate = smth;
    this.coveredString = smth;
};
operatorsSup = ['->', '&', '|', '!'];
operators = {'->': {}, '&': {}, '|': {}, '!': {}};

VAL.prototype = {
    toString: function () {
        return this.defineSym;
    }
};

var cin = function (adr, args) {
    if (args[0][0] === undefined) {
        adr.args = [].slice.call(args);
    } else {
        adr.args = args[0];
    }
};
var operConfirmer = function (str) {
    var create = function () {
        this.assosiate = str;
        this.coveredString = "";
        cin(this, arguments);
    };
    operators[str].assosiate = create;
    return create;
};
var AND = operConfirmer('&');
var OR = operConfirmer('|');
var IMPL = operConfirmer('->');
var NEG = operConfirmer('!');


axioms = [
    "F->X->F",
    "(F->X)->(F->X->Q)->(F->Q)",
    "F->X->F&X",
    "F&X->F",
    "F&X->X",
    "F->F|X",
    "X->F|X",
    "(F->Q)->(X->Q)->(F|X->Q)",
    "(F->X)->(F->!X)->!F",
    "!!F->F"
];
var axiomsStruct = [];
var guessStruct = [];

function isVal(str) {
    if (str[0] === undefined) {
        return (48 <= str && str <= 57 || 64 <= str && str < 90 || 97 <= str && str <= 122);
    }
    for (var i = 0; i < str.length; i++) {
        if (!(48 <= str[i] && str[i] <= 57 || 64 <= str[i] && str[i] < 90 || 97 <= str[i] && str[i] <= 122)) {
            return false;
        }
    }
    return true;
}

function secondStageParse(str, type) {
    var balance = 0;
    var sym = operatorsSup[type];
    if (sym == '!') {
        if (str.charAt(0) == '!') {
            var negTmp = new NEG(secondStageParse(str.slice(1), type));
            negTmp.coveredString = sym+'('+negTmp.args[0].coveredString+')';
            return negTmp;
        }
        else if (str.charAt(0) == '(') {
            //var veryTmp = str.slice(1, str.length - 1);
            return firstStageParse(str.slice(1, str.length - 1));
        }
        else
            return new VAL(str);
    }
    for (i = str.length - 1; i >= 0; i--) {
        if (str.charAt(i) === ')')
            balance++;
        if (str.charAt(i) === '(')
            balance--;
        if (str.charAt(i) === sym && balance === 0) {
            var considerOperator = operators[sym];
            var tmp2 = str.slice(i + 1);
            var fullTmp = new considerOperator.assosiate(secondStageParse(str.slice(0, i), type), secondStageParse(tmp2, type + 1));
            fullTmp.coveredString = '('+fullTmp.args[0].coveredString+sym+fullTmp.args[1].coveredString+')';
            return fullTmp;
        }
    }
    return secondStageParse(str, type + 1);
}
function firstStageParse(str) {
    var balance = 0;
    for (i = 0; i < str.length; i++) {
        if (str.charAt(i) === ')')
            balance++;
        if (str.charAt(i) === '(')
            balance--;
        if (str.charAt(i) === '>' && balance === 0) {
            var tmp2 = str.slice(i + 1);
            var implTmp = new IMPL(secondStageParse(str.slice(0, i - 1), 1), firstStageParse(tmp2));
            implTmp.coveredString = '('+implTmp.args[0].coveredString+'->'+implTmp.args[1].coveredString+')';
            return implTmp;
        }
    }
    return secondStageParse(str, 1);
}

function structExpr(str) {//из строки в структуру
    return firstStageParse(str);
}

var deductionStruct = [];

function check(FXQ1, stru1, stru2) {//проверка на уровне - является ли часть аксиомы похожей на уравнение
    var i;
    var j;
    var tmpFXQ = FXQ1;
    if (stru1.assosiate == stru1.coveredString) {
        if (stru1.assosiate === 'F')
            pointForTmp = 1;
        if (stru1.assosiate === 'X')
            pointForTmp = 2;
        if (stru1.assosiate === 'Q')
            pointForTmp = 3;

        if (tmpFXQ[pointForTmp] === undefined)
            tmpFXQ[pointForTmp] = stru2;

        if (!checkEquality(tmpFXQ[pointForTmp], stru2))
            tmpFXQ[0] = false;

        return tmpFXQ;
    }
    if (stru1.assosiate === stru2.assosiate) {
        for (i = 0; i < stru1.args.length; i++) {
            tmpFXQ = check(tmpFXQ, stru1.args[i], stru2.args[i]);
            if (!tmpFXQ[0]) {
                return tmpFXQ;
            }
        }
        for (j = 1; j < FXQ1.length; j++) {
            if (FXQ1[j] != undefined) {
                if (tmpFXQ[j] != undefined && tmpFXQ[j] != FXQ1[j]) {
                    tmpFXQ[0] = false;
                    return tmpFXQ;
                }
            } else
                FXQ1[j] = tmpFXQ[j];

        }
    }
    else {
        tmpFXQ[0] = false;
    }
    return tmpFXQ;
}
function checkSimilarity(stru1, stru2) {//правда ли что стурктуры похожи?
    var FXQ = [true, undefined, undefined, undefined];
    return check(FXQ, stru1, stru2)[0];
}
function checkEquality(stru1, stru2) {//правда ли что структуры едентичны
    return stru1.coveredString === stru2.coveredString;
}


var solvedDeduction = [];
var solvedReference = [];
function main(str) {
    var i;
    str.replace(/ /g,"");//глобально заменили
    var titleExp = str.split(['|-']);
    var splitedTitle = titleExp[0].split(',');
    var splitedDeduction = titleExp[1].split('\n');

    for (i=0;i != splitedTitle.length && splitedTitle[i] != "";i++)
        guessStruct[i] = structExpr(splitedTitle[i]);
    
    for (i = 0; i < axioms.length; i++)
        axiomsStruct[i] = structExpr(axioms[i]);

    //answer = structExpr(splitedDeduction[0]);

    var answerLine = "";
    for (i=0;i != splitedDeduction.length-1 && splitedDeduction[i+1]!="";i++) {
        deductionStruct[i] = structExpr(splitedDeduction[i+1]);
        //solvedDeduction[i]- "+" - from axioms; "-" from guess; [] from deduction; "0" - wrong
        solvedDeduction[i] = 0;
        var j;
        //check axioms
        for (j = 0; j < axiomsStruct.length && solvedDeduction[i] == 0; j++)
            if (checkSimilarity(axiomsStruct[j], deductionStruct[i]))
                solvedDeduction[i] = j + 1;

        //check guesses
        for (j = 0; j < guessStruct.length && solvedDeduction[i] == 0; j++)
            if (checkEquality(guessStruct[j], deductionStruct[i]))
                solvedDeduction[i] = (-j - 1);

        //find suitable MP values
        solvedReference[i] = [];
        for (i1 = 0; i1 < i; i1++) {
            if (deductionStruct[i1].assosiate == '->') {
                if (checkEquality(deductionStruct[i1].args[1], deductionStruct[i])) {
                    for (i2 = 0; i2 < i1; i2++) {
                        //solvedReference[i] = [];
                        if (checkEquality(deductionStruct[i2], deductionStruct[i1].args[0])) {
                            solvedReference[i][0] = i2;
                            solvedReference[i][1] = i1;
                        }
                    }
                }
            }
        }
        //check MP
        if (solvedDeduction[i] == 0 && solvedDeduction[solvedReference[i][0]] != 0 && solvedDeduction[solvedReference[i][1]] != 0) {//MP if a && a->b a=SD[0] a->b=SD[1]
            if (solvedReference[i][0]!==undefined&&solvedReference[i][1]!==undefined)
            solvedDeduction[i] = [solvedReference[i][0], solvedReference[i][1]];
        }

        //write answer
        answerLine = answerLine + ('(' + i.toString() + ')') + deductionStruct[i].coveredString + ' ';
        if (solvedDeduction[i][0] != undefined)
            answerLine = answerLine + "M.P. " + solvedDeduction[i][0] + ',' + solvedDeduction[i][1];

        if (solvedDeduction[i] == 0)
            answerLine = answerLine + "Not proved";

        if (solvedDeduction[i] > 0)
            answerLine = answerLine + "Cx. akc ." + (solvedDeduction[i] - 1).toString();

        if (solvedDeduction[i] < 0)
            answerLine = answerLine + "Predp. " + (-1 * solvedDeduction[i] - 1).toString();

        answerLine = answerLine + '\n';
    }
    return answerLine
}


var text;
var answerText;
var fs = require('fs');
var fname = "good6.in";
fs.readFile(fname, function (err, logData) {
    if (err)throw err;
    text = logData.toString();
    console.log(text);
    answerText=main(text);
    fs.open("answer.txt","w",0644, function (err, file_handle) {
        fs.write(file_handle,answerText,null,'ascii', function(err,written){
            if (err)throw err;
        })
    });
});


