#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <filesystem>
#include <stdexcept>

#include "slang/ast/Compilation.h"
#include "slang/syntax/SyntaxTree.h"
#include "DataModel.h"
#include "DependencyVisitor.h"
#include "ProgramSlicer.h"
#include "json.hpp"
#include "slang/diagnostics/DiagnosticEngine.h"  
#include "slang/diagnostics/TextDiagnosticClient.h"  

using json = nlohmann::json;

struct TestCase {
        std::string name;
        std::string topModule;
        std::vector<std::string> sourceFiles;
        std::vector<std::string> headerFiles;
        std::string outputPath;
    };

void from_json(const json& j, TestCase& t) {
    // 使用 .at() 确保字段存在，否则会抛出异常
    j.at("name").get_to(t.name);
    j.at("topModule").get_to(t.topModule);
    j.at("sourceFiles").get_to(t.sourceFiles);
    j.at("headerFiles").get_to(t.headerFiles);
    j.at("outputPath").get_to(t.outputPath);
}

// 加载测试套件配置
std::vector<TestCase> loadTestSuite(const std::string& configPath) {
    std::ifstream file(configPath);
    if (!file.is_open()) {
        throw std::runtime_error("Error: Could not open test suite configuration file: " + configPath);
    }
    
    std::cout << "[INFO] Loading test suite from: " << configPath << std::endl;

    json j;
    try {
        file >> j;
    } catch (const json::parse_error& e) {
        throw std::runtime_error("Error parsing JSON file: " + std::string(e.what()));
    }

    // 将整个 JSON 数组转换为 std::vector<TestCase>
    return j.get<std::vector<TestCase>>();
}

// JSON 序列化辅助函数 (保持不变)
void to_json(json& j, const ConditionExpression& expr) {
    j = json{
        {"expression", expr.expression},
        {"involvedSignals", expr.involvedSignals},
        {"involvedParameters", expr.involvedParameters}
    };
}

void to_json(json& j, const ConditionClause& c) {
    j = json{
        {"expr", c.expr},
        {"polarity", c.polarity}
    };
}

void to_json(json& j, const AssignmentInfo& a) {  
    j = json{  
        {"path", a.path},  
        {"drivingSignals", a.drivingSignals},  
        {"sensitivitySignals", a.sensitivitySignals},  // 新增  
        {"file", a.file},  
        {"line", a.line},  
        {"type", a.type},  
        {"logicType", a.logicType},  
        {"conditionDepth", a.conditionDepth}  
    };  
}

void to_json(json& j, const VariableInfo& v) {  
    j = json{  
        {"fullName", v.fullName},  
        {"type", v.type},  
        {"file", v.fileName},  
        {"line", v.line},  
        {"direction", v.direction},  
        {"bitWidth", v.bitWidth},  
        {"assignments", v.assignments},  
        {"fanOut", v.fanOut},  
        {"assignmentCount", v.assignmentCount},  
        {"drivesOutput", v.drivesOutput},  
        {"isControlVariable", v.isControlVariable},  
        {"isSensitivitySignal", v.isSensitivitySignal}  // 新增  
    };  
}

// 核心分析函数 (保持不变)
bool runAnalysis(const std::string& topModule,   
                 const std::vector<std::string>& sourceFiles,  
                 const std::vector<std::string>& headerFiles,  
                 const std::string& outputPath,
                 const SlicingCriterion* criterion = nullptr) {  
      
    std::cout << "--- Analyzing Test Case: " << topModule << " ---" << std::endl;  
    std::cout << "Source files: " << sourceFiles.size() << std::endl;  
    std::cout << "Header files: " << headerFiles.size() << std::endl;  
  
    std::filesystem::path outPath(outputPath);  
    if (outPath.has_parent_path()) {  
        std::filesystem::create_directories(outPath.parent_path());  
    }  

    std::set<std::string> uniqueIncludePaths;
    for (const auto& headerFile : headerFiles) {
        std::filesystem::path headerPath(headerFile);
        if (headerPath.has_parent_path()) {
            uniqueIncludePaths.insert(headerPath.parent_path().string());
        }
    }
    std::vector<std::filesystem::path> finalIncludePaths;
    for (const auto& pathString : uniqueIncludePaths) {
        finalIncludePaths.push_back(std::filesystem::path(pathString));
    }

    // 创建 SourceManager  
    slang::SourceManager sourceManager;  
      
    // 配置预处理器选项,添加 include 路径  
    slang::parsing::PreprocessorOptions ppOptions; 
      
    slang::Bag options;  
    options.set(ppOptions);  
      
    // 重要:使用带 options 的 Compilation 构造函数  
    slang::ast::Compilation compilation(options);  
      
    // 首先添加头文件 - 传递 sourceManager 和 options  
    for (const auto& headerFile : headerFiles) {  
        if (!std::filesystem::exists(headerFile)) {  
            std::cerr << "[WARNING] Header file not found: " << headerFile << std::endl;  
            continue;  
        }  
        // 关键修改:传递 sourceManager 和 options  
        auto tree_expected = slang::syntax::SyntaxTree::fromFile(headerFile, sourceManager, options);  
        if (!tree_expected) {  
            std::cerr << "[WARNING] Failed to parse header file: " << headerFile << std::endl;  
            continue;  
        }  
        compilation.addSyntaxTree(*tree_expected);  
        std::cout << "[INFO] Added header file: " << headerFile << std::endl;  
    }  
      
    // 然后添加源文件 - 同样传递 sourceManager 和 options  
    for (const auto& sourceFile : sourceFiles) {  
        if (!std::filesystem::exists(sourceFile)) {  
            std::cerr << "[ERROR] Source file not found: " << sourceFile << std::endl;  
            return false;  
        }  
        // 关键修改:传递 sourceManager 和 options  
        auto tree_expected = slang::syntax::SyntaxTree::fromFile(sourceFile, sourceManager, options);  
        if (!tree_expected) {  
            std::cerr << "[ERROR] Failed to parse source file: " << sourceFile << std::endl;  
            return false;  
        }  
        compilation.addSyntaxTree(*tree_expected);  
        std::cout << "[INFO] Added source file: " << sourceFile << std::endl;  
    }  
      
    auto& root = compilation.getRoot();  
      
    // 创建诊断引擎和客户端  
    slang::DiagnosticEngine diagEngine(sourceManager);  
    auto textClient = std::make_shared<slang::TextDiagnosticClient>();  
    diagEngine.addClient(textClient);  
      
    // 发出所有诊断  
    for (auto& diag : compilation.getAllDiagnostics())  
        diagEngine.issue(diag);  
      
    // 输出诊断结果  
    std::cout << textClient->getString();  
      
    // 检查是否有错误  
    int numErrors = diagEngine.getNumErrors();  
    if (numErrors > 0) {  
        std::cerr << "[FAILED] Build failed: " << numErrors << " errors\n";  
        return false;  
    }  
      
    std::cout << "[SUCCESS] Build succeeded\n";  
      
    // 查找顶层模块  
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
    visitor.postProcess();  
      
    // 创建 ProgramSlicer 对象  
    ProgramSlicer slicer(visitor.getResults());  
      
    // 创建默认配置    
    SliceConfig config;    
    config.granularity = SliceGranularity::ProceduralBlock;    
    config.filterOptions = SliceFilterOptions::RemoveUnrelatedAssignments;    
    config.contextLines = 0;    
        
    json unifiedOutput; 
    
    std::ofstream outFile(outputPath); 
    unifiedOutput["topModule"] = topModule;    
    unifiedOutput["analysisResults"] = visitor.getResults();    
    outFile << unifiedOutput.dump(2);
    std::cout << "[SUCCESS] Results written to: " << outputPath << std::endl; 
    return true;
    // // 准备txt文件输出  
    // std::stringstream txtOutput;  
    // txtOutput << "========================================\n";  
    // txtOutput << "Program Slices for Module: " << topModule << "\n";  
    // txtOutput << "========================================\n\n";    

    // std::map<std::string, SliceResult> allBackwardSlices;
    // std::map<std::string, SliceResult> allForwardSlices;
    // // 为每个变量生成前向和后向切片    
    // for (const auto& [varName, varInfo] : visitor.getResults()) {    
    //     SlicingCriterion backwardCriterion;    
    //     backwardCriterion.variableName = varName;    
          
    //     SliceResult backwardResult = slicer.backwardSlice(backwardCriterion, config);    
    //     SliceResult forwardResult = slicer.forwardSlice(backwardCriterion, config); 

    //     allBackwardSlices[varName] = backwardResult;
    //     allForwardSlices[varName] = forwardResult;  

    //     std::string backwardCode = slicer.generateMergedCodeForVariable(    
    //         backwardResult, varName, sourceManager);    
    //     std::string forwardCode = slicer.generateMergedCodeForVariable(    
    //         forwardResult, varName, sourceManager);    
    //     // 添加到txt输出  
    //     txtOutput << "========================================\n";  
    //     txtOutput << "Variable: " << varName << "\n";  
    //     txtOutput << "========================================\n\n";  
          
    //     txtOutput << "--- Backward Slice ---\n";  
    //     txtOutput << backwardCode << "\n\n";  
          
    //     txtOutput << "--- Forward Slice ---\n";  
    //     txtOutput << forwardCode << "\n\n";  
          
    //     txtOutput << "----------------------------------------\n\n";   
    //     unifiedOutput["slices"][varName]["backward"]["mergedCode"] = backwardCode;    
    //     unifiedOutput["slices"][varName]["backward"]["metadata"] = {    
    //         {"relevantVariables", backwardResult.relevantVariables},    
    //         {"controlVariables", backwardResult.controlVariables}    
    //     };    
          
    //     unifiedOutput["slices"][varName]["forward"]["mergedCode"] = forwardCode;    
    //     unifiedOutput["slices"][varName]["forward"]["metadata"] = {    
    //         {"relevantVariables", forwardResult.relevantVariables},    
    //         {"controlVariables", forwardResult.controlVariables}    
    //     };    
    // }     
    // std::string depPath = outputPath + ".dependencies.txt";
    // slicer.exportAllDependenciesToTxt(allBackwardSlices, allForwardSlices, depPath); 
    // // 输出到文件    
    // std::ofstream outFile(outputPath);    
    // if (outFile.is_open()) {    
    //     outFile << unifiedOutput.dump(2);    
    //     outFile.close();    
    //     std::cout << "[SUCCESS] Results written to: " << outputPath << std::endl;    
    // }    
    //      // 输出TXT文件  
    // std::string txtPath = outputPath + ".slices.txt";  
    // std::ofstream txtFile(txtPath);  
    // if (txtFile.is_open()) {  
    //     txtFile << txtOutput.str();  
    //     txtFile.close();  
    //     std::cout << "[SUCCESS] Text slices written to: " << txtPath << std::endl;  
    //     return true;  
    // } else {  
    //     std::cerr << "[ERROR] Could not open txt file for writing: " << txtPath << std::endl;  
    //     return false;  
    // }     
    // return false;   
}

/**
 * 主函数，作为测试驱动器
 * 允许用户选择运行单个测试或所有测试。
 */
int main(int argc, char** argv) {


    std::string configFilePath = "/data/fhj/sva-var/rtl_analyzer/analyzer_cpp/tests.json";
    std::vector<TestCase> testSuite;

    try {
        testSuite = loadTestSuite(configFilePath);
    } catch (const std::exception& e) {
        std::cerr << "Fatal Error during test suite loading: " << e.what() << std::endl;
        return 1;
    }

    if (testSuite.empty()) {
        std::cout << "No test cases are currently defined or uncommented in testSuite." << std::endl;
        return 0;
    }
    
    std::cout << "\n========================================" << std::endl;
    std::cout << "Available Test Cases:" << std::endl;
    for (size_t i = 0; i < testSuite.size(); ++i) {
        std::cout << "[" << i + 1 << "] " << testSuite[i].name << std::endl;
    }
    std::cout << "[0] Run ALL Tests" << std::endl;
    std::cout << "========================================" << std::endl;
    std::cout << "Enter selection (1-" << testSuite.size() << ", or 0 for all): ";

    std::string input;
    std::cin >> input;

    std::vector<TestCase> selectedTests;
    int index = -1;

    try {
        index = std::stoi(input);
    } catch (const std::invalid_argument& e) {
        std::cerr << "Invalid input. Please enter a number (0-" << testSuite.size() << ")." << std::endl;
        return 1;
    } catch (const std::out_of_range& e) {
        std::cerr << "Invalid selection: Index out of range." << std::endl;
        return 1;
    }


    if (index == 0) {
        selectedTests = testSuite; // 运行所有测试
        std::cout << "Executing ALL " << testSuite.size() << " test cases." << std::endl;
    } else if (index >= 1 && index <= (int)testSuite.size()) {
        selectedTests.push_back(testSuite[index - 1]); // 索引是 1-based
        std::cout << "Executing selected test: " << testSuite[index - 1].name << std::endl;
    } else {
        std::cerr << "Invalid selection: Index out of range (Must be 0-" << testSuite.size() << ")." << std::endl;
        return 1;
    }

    std::cout << "----------------------------------------" << std::endl;


    // 执行选定的测试
    int successCount = 0;
    for (const auto& testCase : selectedTests) {
        std::cout << "\n========================================" << std::endl;
        std::cout << "Running: " << testCase.name << std::endl;
        std::cout << "========================================" << std::endl;
        
        if (runAnalysis(testCase.topModule, testCase.sourceFiles, testCase.headerFiles, testCase.outputPath)) {
            successCount++;
            std::cout << "✓ PASSED: " << testCase.name << std::endl;
        } else {
            std::cerr << "✗ FAILED: " << testCase.name << std::endl;
        }
    }

    std::cout << "\n========================================" << std::endl;
    std::cout << "Test Suite Finished." << std::endl;
    std::cout << "Passed: " << successCount << " / " << selectedTests.size() << std::endl;
    std::cout << "========================================" << std::endl;

    return (successCount == selectedTests.size()) ? 0 : 1;
}