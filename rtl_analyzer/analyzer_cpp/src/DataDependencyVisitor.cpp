#include "DataDependencyVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/text/SourceManager.h"

// 辅助 Visitor
class SignalCollectorVisitor : public slang::ast::ASTVisitor<SignalCollectorVisitor, true, true> {
public:
    template<typename T> void handle(const T& node) { visitDefault(node); }
    void handle(const slang::ast::NamedValueExpression& expr) {
        const slang::ast::Symbol* symbol = &expr.symbol;
        if (symbol && !symbol->isType()) {
            signals.insert(symbol);
        }
    }
    std::set<const slang::ast::Symbol*> signals;
};

// --- 新增一个辅助函数，用于将端口方向枚举转换为字符串 ---
static std::string directionToString(slang::ast::ArgumentDirection dir) {
    switch (dir) {
        case slang::ast::ArgumentDirection::In:
            return "input";
        case slang::ast::ArgumentDirection::Out:
            return "output";
        case slang::ast::ArgumentDirection::InOut:
            return "inout";
        default:
            return "unknown";
    }
}

// --- 私有辅助函数：如果变量不存在，则创建并填充其信息 ---
VariableInfo& DataDependencyVisitor::getOrAddVariable(const slang::ast::Symbol& symbol) {  
    std::string path = symbol.getHierarchicalPath();  
    if (variables.find(path) == variables.end()) {  
        VariableInfo info;  
        info.fullName = path;  
  
        // 对于端口,使用 internalSymbol 的类型  
        if (const auto* portSymbol = symbol.as_if<slang::ast::PortSymbol>()) {  
            info.direction = directionToString(portSymbol->direction);  
              
            // 获取端口的内部符号  
            if (portSymbol->internalSymbol) {  
                const auto* internalValue = portSymbol->internalSymbol->as_if<slang::ast::ValueSymbol>();  
                if (internalValue) {  
                    const slang::ast::Type& type = internalValue->getType();  
                    info.type = type.toString();  
                    info.bitWidth = type.getBitWidth();  
                }  
            }  
        }  
        // 对于普通变量  
        else if (const auto* valueSymbol = symbol.as_if<slang::ast::ValueSymbol>()) {  
            const slang::ast::Type& type = valueSymbol->getType();  
            info.type = type.toString();  
            info.bitWidth = type.getBitWidth();  
        }  
  
        // 提取位置信息  
        const slang::ast::Scope* scope = symbol.getParentScope();  
        if (scope) {  
            auto& comp = scope->getCompilation();  
            auto* sm = comp.getSourceManager();  
            if (sm && symbol.location) {  
                info.fileName = std::string(sm->getFileName(symbol.location));  
                info.line = sm->getLineNumber(symbol.location);  
            }  
        }  
        variables[path] = info;  
    }  
    return variables.at(path);  
}

// --- 为 VariableSymbol 实现 handle ---
void DataDependencyVisitor::handle(const slang::ast::VariableSymbol& symbol) {
    getOrAddVariable(symbol);
    visitDefault(symbol);
}

// --- 为 PortSymbol 实现 handle ---
void DataDependencyVisitor::handle(const slang::ast::PortSymbol& symbol) {
    getOrAddVariable(symbol);
    visitDefault(symbol);
}

// --- 处理赋值语句 ---
void DataDependencyVisitor::handle(const slang::ast::AssignmentExpression& expr) {
    const slang::ast::Symbol* lhsSymbol = expr.left().getSymbolReference();
    if (!lhsSymbol) {
        visitDefault(expr);
        return;
    }
    
    VariableInfo& lhsInfo = getOrAddVariable(*lhsSymbol);

    SignalCollectorVisitor rhsVisitor;
    expr.right().visit(rhsVisitor);
    
    for (const auto* rhsSymbol : rhsVisitor.signals) {
        VariableInfo& rhsInfo = getOrAddVariable(*rhsSymbol);
        lhsInfo.fanInData.insert(rhsInfo.fullName);
        rhsInfo.fanOut.insert(lhsInfo.fullName);
    }
    visitDefault(expr);
}

// --- 处理模块实例化和端口连接 ---
void DataDependencyVisitor::handle(const slang::ast::InstanceSymbol& symbol) {
    for (auto* portConnection : symbol.getPortConnections()) {
        const slang::ast::Symbol& internalPort = portConnection->port;
        const slang::ast::Expression* externalExpr = portConnection->getExpression();
        if (!externalExpr) continue;
        
        VariableInfo& internalPortInfo = getOrAddVariable(internalPort);

        SignalCollectorVisitor externalSignalVisitor;
        externalExpr->visit(externalSignalVisitor);

        for (const auto* externalSymbol : externalSignalVisitor.signals) {
            VariableInfo& externalInfo = getOrAddVariable(*externalSymbol);
            auto direction = internalPort.as<slang::ast::PortSymbol>().direction;
            
            if (direction != slang::ast::ArgumentDirection::In) { // Out or InOut
                externalInfo.fanInData.insert(internalPortInfo.fullName);
                internalPortInfo.fanOut.insert(externalInfo.fullName);
            }
            if (direction != slang::ast::ArgumentDirection::Out) { // In or InOut
                // --- 【终极修正】---
                // 将错误的 'internalInfo' 改为正确的 'internalPortInfo'
                internalPortInfo.fanInData.insert(externalInfo.fullName);
                externalInfo.fanOut.insert(internalPortInfo.fullName);
            }
        }
    }
    visitDefault(symbol);
}