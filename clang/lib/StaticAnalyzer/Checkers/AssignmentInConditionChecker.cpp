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
    void checkAssignment(const Stmt *Statement, CheckerContext &Ctx) const;

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

void AssignmentInConditionChecker::checkAssignment(const Stmt *Statement, CheckerContext &Ctx) const {
    const Expr* expr=dyn_cast<Expr>(Statement);

    //class of expresion that contains assignment will be ImplicitCastExpr
    //type of right operand comma operator has to be bool
    if(const ImplicitCastExpr* implicitExpr = dyn_cast_or_null<ImplicitCastExpr>(expr)){
        if(! (implicitExpr->getBeginLoc()==implicitExpr->getEndLoc())){
            ReportBug(expr,"Assignment is used as branch condition",Ctx);
            return;
        }
    }


    //we expect left operand of comma operator to produce some side effect
    //if that is not a case we report a warning
    if(const BinaryOperator *binOp = dyn_cast<BinaryOperator>(expr)) {
        if(binOp->isCommaOp()){
            expr = binOp->getLHS();

            while(const BinaryOperator *binOperator = dyn_cast_or_null<BinaryOperator>(expr)) {
                if(!binOperator->isCommaOp()){
                    if(!(binOperator->isAssignmentOp() || binOperator->isCompoundAssignmentOp())){
                        ReportBug(expr,"Statement produces no effect",Ctx);
                        return;
                    }
                }
        
                Expr* leftExpr = binOperator->getLHS();
                if(BinaryOperator *leftOp = dyn_cast<BinaryOperator>(leftExpr)) {
                    if(!leftOp->isCommaOp()){
                        if(!(leftOp->isAssignmentOp() || leftOp->isCompoundAssignmentOp())){
                            ReportBug(expr,"Statement produces no effect",Ctx);
                            return;
                        }
                    }
                }

                Expr* rightExpr = binOperator->getRHS();
                if(BinaryOperator *rightOp = dyn_cast<BinaryOperator>(rightExpr)) {
                    if(!(rightOp->isAssignmentOp() || rightOp->isCompoundAssignmentOp())){
                        ReportBug(rightExpr,"Statement produces no effect",Ctx);
                        return;    
                    }
                }
                expr = leftExpr;
            }
        }      
    }
}


void AssignmentInConditionChecker::checkBranchCondition(const Stmt *Condition, CheckerContext &Ctx) const {
    
    checkAssignment(Condition, Ctx);

}

void ento::registerAssignmentInConditionChecker(CheckerManager &mgr) {
    mgr.registerChecker<AssignmentInConditionChecker>();
}

bool ento::shouldRegisterAssignmentInConditionChecker(const CheckerManager &mgr) {
    return true;
}