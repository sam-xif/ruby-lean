p [require('forwardable'),require('forwardable'),require('forwardable.rb')]
p [require('uri'),require('uri.rb'),require('sorbet-runtime'),require('sorbet-runtime.rb')]
p [require('pathname'),require('pathname.rb'),require('pathname.so')]
p [require('json'),require('json.rb')]
p [Forwardable.class,URI.class,T.class,Pathname.class]

p [respond_to?(:require), respond_to?(:require,true),Object.private_method_defined?(:require)]
begin;Object.new.require('forwardable');rescue NoMethodError=>e;p e.class;end
p require('forwardable')

class Object;alias load_feature require;end
p [load_feature('uri'),load_feature('uri.rb')]
p URI.decode_www_form_component('a+b')

p [Pathname.class,Pathname.method_defined?(:to_str),require("pathname"),require("pathname")]

p [defined?($LOADED_FEATURES),defined?($LOAD_PATH),defined?($"),defined?($:),defined?($-I)]
