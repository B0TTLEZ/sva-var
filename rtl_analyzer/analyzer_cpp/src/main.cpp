#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <filesystem>

#include "slang/ast/Compilation.h"
#include "slang/syntax/SyntaxTree.h"
#include "DataModel.h"
#include "DependencyVisitor.h"
#include "json.hpp"

using json = nlohmann::json;

// --- JSON 序列化函数 ---
void to_json(json& j, const ConditionExpression& expr) {
    j = {
        {"expression", expr.expression},
        {"involvedSignals", expr.involvedSignals}
    };
}

void to_json(json& j, const ConditionClause& c) {
    j = {
        {"expr", c.expr},
        {"polarity", c.polarity}
    };
}

void to_json(json& j, const AssignmentInfo& a) {
    j = {
        {"path", a.path},
        {"drivingSignals", a.drivingSignals},
        {"file", a.file},
        {"line", a.line},
        {"type", a.type}
    };
}

void to_json(json& j, const VariableInfo& v) {
    j = {
        {"fullName", v.fullName},
        {"type", v.type},
        {"file", v.fileName},
        {"line", v.line},
        {"direction", v.direction},
        {"bitWidth", v.bitWidth},
        {"assignments", v.assignments},
        {"fanOut", v.fanOut}
    };
}

// --- 核心分析函数 ---
bool runAnalysis(const std::string& topModule, 
                 const std::vector<std::string>& filesToParse, 
                 const std::string& outputPath) {
    
    std::cout << "--- Analyzing Test Case: " << topModule << " ---" << std::endl;

    std::filesystem::path outPath(outputPath);
    if (outPath.has_parent_path()) {
        std::filesystem::create_directories(outPath.parent_path());
    }

    slang::ast::Compilation compilation;
    for (const auto& file : filesToParse) {
        if (!std::filesystem::exists(file)) {
            std::cerr << "[ERROR] Input file not found: " << file << std::endl;
            return false;
        }
        auto tree_expected = slang::syntax::SyntaxTree::fromFile(file);
        if (!tree_expected) {
            std::cerr << "[ERROR] Failed to parse file: " << file << std::endl;
            return false;
        }
        compilation.addSyntaxTree(*tree_expected);
    }
    
    auto& root = compilation.getRoot();
    const slang::ast::InstanceSymbol* top = nullptr;
    for (auto inst : root.topInstances) {
        if (inst->name == topModule) {
            top = inst;
            break;
        }
    }
    
    if (!top) {
        std::cerr << "[ERROR] Top module '" << topModule << "' not found." << std::endl;
        return false;
    }
    
    DependencyVisitor visitor;
    top->visit(visitor);
    visitor.postProcess(); // 运行后处理来构建 FanOut
    
    json resultJson = visitor.getResults();

    std::ofstream outFile(outputPath);
    if (outFile.is_open()) {
        outFile << resultJson.dump(4); 
        outFile.close();
        std::cout << "[SUCCESS] Results written to: " << outputPath << std::endl;
        return true;
    } else {
        std::cerr << "[ERROR] Could not open output file for writing: " << outputPath << std::endl;
        return false;
    }
}

// 主函数，作为测试驱动器
int main(int argc, char** argv) {
    struct TestCase {
        std::string name;
        std::string topModule;
        std::vector<std::string> files;
        std::string outputPath;
    };

std::vector<TestCase> testSuite = {
        // --- 现有测试用例 (路径已确认) ---
        {
            "Basic Dataflow",
            "test_basic",
            {"../test_suite/1_basic_dataflow/test_basic.sv"},
            "../../results/1_basic_dataflow.json"
        },
        {
            "Sequential Controlflow",
            "test_sequential",
            {"../test_suite/2_sequential_controlflow/test_sequential.sv"},
            "../../results/2_sequential_controlflow.json"
        },
        {
            "Module Hierarchy",
            "top_module",
            {
                "../test_suite/3_module_hierarchy/sub_module.sv",
                "../test_suite/3_module_hierarchy/top_module.sv"
            },
            "../../results/3_module_hierarchy.json"
        },
        
        // --- 新增测试用例 (根据您的截图更新) ---
        {
            "Complex Conditions",
            "test_complex_conditions", // 假设顶层模块名与文件名相同
            {"../test_suite/4_complex_conditions/test_complex_conditions.sv"},
            "../../results/4_complex_conditions.json"
        },
        {
            "Complex Hierarchy",
            "top_hierarchy", // 假设顶层模块名
            {
                // 注意：您需要提供这个测试用例中所有 .sv 文件的正确名称
                // 我暂时用 'heirachy.sv' 作为占位符，您可能需要修改
                "../test_suite/5_complex_hierarchy/hierarchy.sv" 
            },
            "../../results/5_complex_hierarchy.json"
        },
        {
            "Control Flow",
            "test_control_flow", // 假设顶层模块名与文件名相同
            {"../test_suite/6_controlflow/test_control_flow.sv"},
            "../../results/6_controlflow.json"
        },
        {
            "Data Types",
            "test_data_types", // 假设顶层模块名与文件名相同
            {"../test_suite/7_datatypes/test_data_types.sv"},
            "../../results/7_datatypes.json"
        }
    };

    int successCount = 0;
    for (const auto& testCase : testSuite) {
        if (runAnalysis(testCase.topModule, testCase.files, testCase.outputPath)) {
            successCount++;
        } else {
            std::cerr << "--- Test Case FAILED: " << testCase.name << " ---" << std::endl;
        }
        std::cout << "\n";
    }

    std::cout << "========================================" << std::endl;
    std::cout << "Test Suite Finished." << std::endl;
    std::cout << "Passed: " << successCount << " / " << testSuite.size() << std::endl;
    std::cout << "========================================" << std::endl;

    return (successCount == testSuite.size()) ? 0 : 1;
}