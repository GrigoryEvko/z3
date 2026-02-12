 /*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  lackr_model_converter_lazy.h

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
 --*/
#pragma once

#include "ast/converters/model_converter.h"
#include "ackermannization/lackr_model_constructor.h"

model_converter * mk_lackr_model_converter_lazy(ast_manager & m, const lackr_model_constructor_ref& model_constructor);

