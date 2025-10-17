#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <filesystem>

#include "slang/ast/Compilation.h"
#include "slang/syntax/SyntaxTree.h"

#include "DataDependencyVisitor.h" // <-- 已更新
#include "ControlFlowVisitor.h"
#include "json.hpp"

using json = nlohmann::json;

// JSON 序列化函数
void to_json(json& j, const VariableInfo& var_info) {
    j = json{
        {"fullName", var_info.fullName},
        {"type", var_info.type},
        {"file", var_info.fileName},
        {"line", var_info.line},
        {"direction", var_info.direction},
        {"bitWidth", var_info.bitWidth},
        {"fanInControl", var_info.fanInControl},
        {"fanInData", var_info.fanInData},
        {"fanOut", var_info.fanOut}
    };
}

// 核心分析函数
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
    
    // 1. 运行数据依赖分析
    DataDependencyVisitor dataVisitor; // <-- 已更新
    top->visit(dataVisitor);
    
    // 2. 运行控制依赖分析
    ControlFlowVisitor controlVisitor;
    top->visit(controlVisitor);
    
    // 3. 合并结果
    auto finalResults = dataVisitor.getMutableResults(); // <-- 已更新
    const auto& controlMap = controlVisitor.getControlMap();

    for (const auto& [controlledSignal, controlSignals] : controlMap) {
        if (finalResults.count(controlledSignal)) {
            finalResults[controlledSignal].fanInControl.insert(controlSignals.begin(), controlSignals.end());
        }
    }

    // 4. 输出最终的 JSON
    json resultJson = finalResults;

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