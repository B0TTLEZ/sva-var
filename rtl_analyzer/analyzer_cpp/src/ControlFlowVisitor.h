#pragma once

#include <string>
#include <set>
#include <map>
#include <vector>

#include "DataModel.h" 

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/statements/ConditionalStatements.h"


class ControlFlowVisitor : public slang::ast::ASTVisitor<ControlFlowVisitor, true, true> {
public:
    ControlFlowVisitor() = default;

    template<typename T>
    void handle(const T& node) {
        visitDefault(node);
    }

    void handle(const slang::ast::ConditionalStatement& stmt);
    void handle(const slang::ast::CaseStatement& stmt);

    const ControlMap& getControlMap() const {
        return controlMap;
    }

private:
    ControlMap controlMap;
};