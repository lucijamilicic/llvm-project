#include "llvm/ADT/StringRef.h"
#include "clang/AST/ParentMap.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Type.h"
#include "clang/AST/Stmt.h"
#include "clang/Basic/TypeTraits.h"
#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include <iostream>
#include <optional>

using namespace clang;
using namespace ento;

namespace {

class AssignmentInConditionChecker: public Checker<check::BranchCondition> {

    mutable std::unique_ptr<BuiltinBug> BT;
    void ReportBug(const Expr *Ex, const std::string &Msg, CheckerContext &C) const;
    static bool isAssignment(const Expr* expr);
    static bool checkCommaOp(const Expr* expr);


    public:
        void checkBranchCondition(const Stmt *Condition, CheckerContext &Ctx) const;
    };
}

void AssignmentInConditionChecker::ReportBug(const Expr *Ex, const std::string &Msg, CheckerContext &C) const {

    if (ExplodedNode *N = C.generateNonFatalErrorNode()) {
        if (!BT){
            BT.reset(new BuiltinBug(this, "***BUGG***"));
        }

        C.emitReport(std::make_unique<PathSensitiveBugReport>(*BT, Msg.c_str(), N));
    }
}

void AssignmentInConditionChecker::checkBranchCondition(const Stmt *Statement, CheckerContext &Ctx) const {
    const Expr* expr=dyn_cast<Expr>(Statement);

    if(isAssignment(expr)){
        ReportBug(expr,"Assignment is used as branch condition",Ctx);
    }
    // class of condition statement that contains assignment will be ImplicitCastExpr
    // recursive analysis
    else if(const ImplicitCastExpr* implicitExpr = dyn_cast_or_null<ImplicitCastExpr>(expr)){
        const Expr * e = implicitExpr->getSubExprAsWritten();

        checkBranchCondition(e, Ctx);
    }
    //we expect right operand of comma operator to be a condition and left operand to produce some side effect
    //if that is not a case we report a warning
    else if(const BinaryOperator *binOp = dyn_cast<BinaryOperator>(expr)){
        if(binOp->isCommaOp()){
            checkBranchCondition(binOp->getRHS(), Ctx);

            if(checkCommaOp(binOp->getLHS())){
                ReportBug(expr,"Statement produces no effect",Ctx);
            }
        }
    }
    // recursive analysis for expression inside parentheses
    else if(const ParenExpr *p = dyn_cast<ParenExpr>(expr)){
        checkBranchCondition(p->getSubExpr(), Ctx);
        return;
    }

}

// x++, x--, ... should not report -> checks only for binary operators
bool AssignmentInConditionChecker::isAssignment(const Expr* expr){
    if(const BinaryOperator *binOp = dyn_cast_or_null<BinaryOperator>(expr)){
        if(binOp->isAssignmentOp() || binOp->isCompoundAssignmentOp())
            return true;
    }

    return false;
}

// checks if any of left operands of comma operator does not produce side effect
bool AssignmentInConditionChecker::checkCommaOp(const Expr* expr){
    if(isa<UnaryOperator>(expr)){
        return false;
    }

    if(const BinaryOperator *binOp = dyn_cast<BinaryOperator>(expr)){
        if(binOp->isCommaOp()){
            return checkCommaOp(binOp->getLHS()) || checkCommaOp(binOp->getRHS());
        }
    }

    if(const ParenExpr *p = dyn_cast<ParenExpr>(expr)){
        return checkCommaOp(p->getSubExpr());
    }

    return !isAssignment(expr);

}

void ento::registerAssignmentInConditionChecker(CheckerManager &mgr) {
    mgr.registerChecker<AssignmentInConditionChecker>();
}

bool ento::shouldRegisterAssignmentInConditionChecker(const CheckerManager &mgr) {
    return true;
}